{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

module Verifier.SAW.Heapster.TypedCrucible where

import Data.Maybe
-- import Data.Text hiding (length, map, concat, findIndex, foldr, foldl, maximum, take, last)
import Data.List (findIndex, maximumBy, filter)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Type.Equality
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Kind
import GHC.TypeLits
import What4.ProgramLoc
import What4.FunctionName

import Control.Lens hiding ((:>),Index)
import Control.Monad.State
import Control.Monad.Reader

import Text.PrettyPrint.ANSI.Leijen (pretty)

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap
import Data.Binding.Hobbits.Mb (mbMap2)

import Data.Parameterized.Context hiding ((:>), empty, take, view, last)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import Data.Parameterized.TraversableF

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), empty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- import Data.Parameterized.TraversableFC
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.Extension.Safety
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.CFG.Extension.Safety
import Lang.Crucible.Analysis.Fixpoint.Components
import qualified What4.Partial.AssertionTree as AT

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.Implication

import Debug.Trace

-- | Make a program location with "internal" posiotion that has the same
-- function name as another location
-- FIXME: figure out where to put this
internalLoc :: ProgramLoc -> ProgramLoc
internalLoc loc = mkProgramLoc (plFunction loc) InternalPos


-- FIXME: move to Hobbits
extMbMulti :: MapRList f ctx2 -> Mb ctx1 a -> Mb (ctx1 :++: ctx2) a
extMbMulti ns mb = mbCombine $ fmap (nuMulti ns . const) mb


----------------------------------------------------------------------
-- * Typed Jump Targets and Function Handles
----------------------------------------------------------------------

-- | During type-checking, we convert Crucible registers to variables
newtype TypedReg tp = TypedReg { typedRegVar :: ExprVar tp }

instance PermPretty (TypedReg tp) where
  permPrettyM = permPrettyM . typedRegVar

-- | A sequence of typed registers
data TypedRegs ctx where
  TypedRegsNil :: TypedRegs RNil
  TypedRegsCons :: TypedRegs ctx -> TypedReg a -> TypedRegs (ctx :> a)

-- | Extract out a sequence of variables from a 'TypedRegs'
typedRegsToVars :: TypedRegs ctx -> MapRList Name ctx
typedRegsToVars TypedRegsNil = MNil
typedRegsToVars (TypedRegsCons regs (TypedReg x)) = typedRegsToVars regs :>: x

-- | Turn a sequence of typed registers into a variable substitution
typedRegsToVarSubst :: TypedRegs ctx -> PermVarSubst ctx
typedRegsToVarSubst = permVarSubstOfNames . typedRegsToVars

-- | A typed register along with its value if that is known statically
data RegWithVal a
  = RegWithVal (TypedReg a) (PermExpr a)
  | RegNoVal (TypedReg a)

-- | Get the expression for a 'RegWithVal', even if it is only the variable for
-- its register value when it has no statically-known value
regWithValExpr :: RegWithVal a -> PermExpr a
regWithValExpr (RegWithVal _ e) = e
regWithValExpr (RegNoVal (TypedReg x)) = PExpr_Var x

-- | A type-checked Crucible expression is a Crucible 'Expr' that uses
-- 'TypedReg's for variables. As part of type-checking, these typed registers
-- (which are the inputs to the expression) as well as the final output value of
-- the expression are annotated with equality permissions @eq(e)@ if their
-- values can be statically represented as permission expressions @e@.
data TypedExpr ext tp =
  TypedExpr (App ext RegWithVal tp) (Maybe (PermExpr tp))

-- | A "typed" function handle is a normal function handle along with a context
-- of ghost variables
data TypedFnHandle ghosts args ret where
  TypedFnHandle :: CruCtx ghosts -> FnHandle cargs ret ->
                   TypedFnHandle ghosts (CtxToRList cargs) ret

-- | Extract out the context of ghost arguments from a 'TypedFnHandle'
typedFnHandleGhosts :: TypedFnHandle ghosts args ret -> CruCtx ghosts
typedFnHandleGhosts (TypedFnHandle ghosts _) = ghosts

-- | Extract out the context of regular arguments from a 'TypedFnHandle'
typedFnHandleArgs :: TypedFnHandle ghosts args ret -> CruCtx args
typedFnHandleArgs (TypedFnHandle _ h) = mkCruCtx $ handleArgTypes h

-- | Extract out the context of all arguments of a 'TypedFnHandle', including
-- the lifetime argument
typedFnHandleAllArgs :: TypedFnHandle ghosts args ret -> CruCtx (ghosts :++: args)
typedFnHandleAllArgs h =
  appendCruCtx (typedFnHandleGhosts h) (typedFnHandleArgs h)


-- | Extract out the return type of a 'TypedFnHandle'
typedFnHandleRetType :: TypedFnHandle ghosts args ret -> TypeRepr ret
typedFnHandleRetType (TypedFnHandle _ h) = handleReturnType h


-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' (which is just an index
-- into the @blocks@ context of contexts) plus an 'Int' specifying which entry
-- point to that block. Each entry point also takes an extra set of "ghost"
-- arguments, not extant in the original program, that are needed to express
-- input and output permissions.
data TypedEntryID (blocks :: RList (RList CrucibleType))
     (args :: RList CrucibleType) ghosts =
  TypedEntryID { entryBlockID :: Member blocks args,
                 entryGhosts :: CruCtx ghosts,
                 entryIndex :: Int }

memberLength :: Member a as -> Int
memberLength Member_Base = 0
memberLength (Member_Step memb) = 1 + memberLength memb

entryIDIndices :: TypedEntryID blocks args ghosts -> (Int, Int)
entryIDIndices (TypedEntryID memb _ ix) = (memberLength memb, ix)

instance Show (TypedEntryID blocks args ghosts) where
  show entryID = "<entryID " ++ show (entryIDIndices entryID) ++ ">"

instance TestEquality (TypedEntryID blocks args) where
  testEquality (TypedEntryID memb1 ghosts1 i1) (TypedEntryID memb2 ghosts2 i2)
    | memb1 == memb2 && i1 == i2 = testEquality ghosts1 ghosts2
  testEquality _ _ = Nothing

-- | A typed target for jump and branch statements, where the arguments
-- (including top-level function arguments and ghost arguments) are given with
-- their permissions as a 'DistPerms'
data TypedJumpTarget blocks tops ps where
     TypedJumpTarget ::
       TypedEntryID blocks args ghosts ->
       Proxy tops -> CruCtx args ->
       DistPerms ((tops :++: args) :++: ghosts) ->
       TypedJumpTarget blocks tops ((tops :++: args) :++: ghosts)


$(mkNuMatching [t| forall tp. TypedReg tp |])
$(mkNuMatching [t| forall tp. RegWithVal tp |])
$(mkNuMatching [t| forall ctx. TypedRegs ctx |])

instance NuMatchingAny1 TypedReg where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 RegWithVal where
  nuMatchingAny1Proof = nuMatchingProof

type NuMatchingExtC ext =
  (NuMatchingAny1 (ExprExtension ext RegWithVal),
   NuMatching (AssertionClassifier ext RegWithVal)
  -- (NuMatchingAny1 (ExprExtension ext TypedReg)
   -- , NuMatchingAny1 (StmtExtension ext TypedReg))
  )

$(mkNuMatching [t| forall ext tp. NuMatchingExtC ext => TypedExpr ext tp |])
$(mkNuMatching [t| forall ghosts args ret. TypedFnHandle ghosts args ret |])
$(mkNuMatching [t| forall blocks ghosts args. TypedEntryID blocks args ghosts |])
$(mkNuMatching [t| forall blocks tops ps_in. TypedJumpTarget blocks tops ps_in |])

instance NuMatchingAny1 (TypedJumpTarget blocks tops) where
  nuMatchingAny1Proof = nuMatchingProof

-- FIXME: Hobbits mkNuMatching cannot handle empty types
-- $(mkNuMatching [t| forall f tp. EmptyExprExtension f tp |])

instance NuMatching (EmptyExprExtension f tp) where
  nuMatchingProof = unsafeMbTypeRepr


instance NuMatchingAny1 (EmptyExprExtension f) where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| AVXOp1 |])
$(mkNuMatching [t| forall f tp. NuMatchingAny1 f => ExtX86 f tp |])
$(mkNuMatching [t| forall arch f tp. NuMatchingAny1 f =>
                LLVMExtensionExpr arch f tp |])

instance NuMatchingAny1 f => NuMatchingAny1 (LLVMExtensionExpr arch f) where
  nuMatchingAny1Proof = nuMatchingProof

{-
$(mkNuMatching [t| forall w f tp. NuMatchingAny1 f => LLVMStmt w f tp |])
-}

instance Closable (TypedEntryID blocks args ghosts) where
  toClosed (TypedEntryID entryBlockID entryGhosts entryIndex) =
    $(mkClosed [| TypedEntryID |]) `clApply` toClosed entryBlockID `clApply`
    toClosed entryGhosts `clApply` toClosed entryIndex

instance Liftable (TypedEntryID blocks args ghosts) where
  mbLift [nuP| TypedEntryID entryBlockID entryGhosts entryIndex |] =
    TypedEntryID { entryBlockID = mbLift entryBlockID,
                   entryGhosts = mbLift entryGhosts,
                   entryIndex = mbLift entryIndex }


----------------------------------------------------------------------
-- * Typed Crucible Statements
----------------------------------------------------------------------

-- | Typed Crucible statements with the given Crucible syntax extension and the
-- given set of return values
data TypedStmt ext (rets :: RList CrucibleType) ps_in ps_out where

  -- | Assign a pure Crucible expressions to a register, where pure here means
  -- that its translation to SAW will be pure (i.e., no LLVM pointer operations)
  TypedSetReg :: TypeRepr tp -> TypedExpr ext tp ->
                 TypedStmt ext (RNil :> tp) RNil (RNil :> tp)

  -- | Assign a pure permissions expression to a register
  TypedSetRegPermExpr :: TypeRepr tp -> PermExpr tp ->
                         TypedStmt ext (RNil :> tp) RNil (RNil :> tp)

  -- | Function call (FIXME: document the type here)
  TypedCall :: args ~ CtxToRList cargs =>
               TypedReg (FunctionHandleType cargs ret) ->
               FunPerm ghosts args ret ->
               PermExprs ghosts -> TypedRegs args ->
               TypedStmt ext (RNil :> ret)
               (args :> FunctionHandleType cargs ret)
               (args :> ret)

  -- | Begin a new lifetime:
  --
  -- > . -o ret:lowned(nil)
  BeginLifetime :: TypedStmt ext (RNil :> LifetimeType)
                   RNil (RNil :> LifetimeType)

  -- | End a lifetime, consuming the minimal lifetime ending permissions for the
  -- lifetime as well as all permissions that still contain the lifetime, and
  -- returning the permissions stored in the @lowned@ permission:
  --
  -- > minLtEndperms(ps) * ps_l * l:lowned(ps) -o ps
  EndLifetime :: ExprVar LifetimeType -> DistPerms ps ->
                 PermExpr PermListType -> DistPerms ps_l ->
                 TypedStmt ext RNil (ps :> LifetimeType :++: ps_l) ps

  -- | Assert a boolean condition, printing the given string on failure
  TypedAssert :: TypedReg BoolType -> TypedReg StringType ->
                 TypedStmt ext RNil RNil RNil

  -- | LLVM-specific statement
  TypedLLVMStmt :: TypedLLVMStmt (ArchWidth arch) ret ps_in ps_out ->
                   TypedStmt (LLVM arch) (RNil :> ret) ps_in ps_out


data TypedLLVMStmt w ret ps_in ps_out where
  -- | Assign an LLVM word (i.e., a pointer with block 0) to a register
  --
  -- Type: @. -o ret:eq(word(x))@
  ConstructLLVMWord :: (1 <= w2, KnownNat w2) =>
                       TypedReg (BVType w2) ->
                       TypedLLVMStmt w (LLVMPointerType w2)
                       RNil
                       (RNil :> LLVMPointerType w2)

  -- | Assert that an LLVM pointer is a word, and return 0. This is the typed
  -- version of 'LLVM_PointerBlock' when we know the input is a word, i.e., has
  -- a pointer block value of 0.
  --
  -- Type: @x:eq(word(y)) -o ret:eq(0)@
  AssertLLVMWord :: (1 <= w2, KnownNat w2) =>
                    TypedReg (LLVMPointerType w2) -> PermExpr (BVType w2) ->
                    TypedLLVMStmt w NatType
                    (RNil :> LLVMPointerType w2)
                    (RNil :> NatType)


  -- | Assert that an LLVM pointer is a pointer
  --
  -- Type: @x:is_llvmptr -o .@
  AssertLLVMPtr :: (1 <= w2, KnownNat w2) => TypedReg (LLVMPointerType w2) ->
                   TypedLLVMStmt w UnitType (RNil :> LLVMPointerType w2) RNil

  -- | Destruct an LLVM word into its bitvector value, which should equal the
  -- given expression
  --
  -- Type: @x:eq(word(e)) -o ret:eq(e)@
  DestructLLVMWord :: (1 <= w2, KnownNat w2) =>
                      TypedReg (LLVMPointerType w2) -> PermExpr (BVType w2) ->
                      TypedLLVMStmt w (BVType w2)
                      (RNil :> LLVMPointerType w2)
                      (RNil :> BVType w2)

  -- | Add an offset to an LLVM value
  --
  -- Type: @. -o ret:eq(x &+ off)@
  OffsetLLVMValue :: (1 <= w2, KnownNat w2) =>
                     TypedReg (LLVMPointerType w2) -> PermExpr (BVType w2) ->
                     TypedLLVMStmt w (LLVMPointerType w2)
                     RNil
                     (RNil :> LLVMPointerType w2)

  -- | Load a machine value from the address pointed to by the given pointer
  -- using the supplied field permission. Some set of permissions @ps@ can be on
  -- the stack below the field permission, and these are preserved. The lifetime
  -- of the field permission must also be proved to be current; the permissions
  -- for this are on the top of the stack and are also preserved.
  --
  -- Type:
  -- > ps, x:ptr((rw,0) |-> p), cur_ps
  -- > -o ps, x:ptr((rw,0) |-> eq(ret)), ret:p, cur_ps
  TypedLLVMLoad :: (1 <= w, KnownNat w) =>
                   TypedReg (LLVMPointerType w) -> LLVMFieldPerm w ->
                   DistPerms ps -> LifetimeCurrentPerms ps_l ->
                   TypedLLVMStmt w (LLVMPointerType w)
                   (ps :> LLVMPointerType w :++: ps_l)
                   (ps :> LLVMPointerType w :> LLVMPointerType w :++: ps_l)

  -- | Store a machine value to the address pointed to by the given pointer
  -- using the supplied field permission, which also specifies the offset from
  -- the pointer where the store occurs. Some set of permissions @ps@ can be on
  -- the stack below the field permission, and these are preserved. The lifetime
  -- of the field permission must also be proved to be current; the permissions
  -- for this are on the top of the stack and are also preserved.
  --
  -- Type:
  -- > ps, x:ptr((rw,0) |-> p), cur_ps
  -- > -o ps, x:ptr((rw,0) |-> eq(e)), cur_ps
  TypedLLVMStore :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                    LLVMFieldPerm w -> PermExpr (LLVMPointerType w) ->
                    DistPerms ps -> LifetimeCurrentPerms ps_l ->
                    TypedLLVMStmt w UnitType
                    (ps :> LLVMPointerType w :++: ps_l)
                    (ps :> LLVMPointerType w :++: ps_l)

  -- | Allocate an object of the given size on the given LLVM frame
  --
  -- Type:
  -- > fp:frame(ps) -o fp:frame(ps,(ret,i)),
  -- >                 ret:ptr((w,0) |-> true, (w,M) |-> true,
  -- >                         ..., (w,M*(i-1)) |-> true)
  --
  -- where @M@ is the machine word size in bytes
  TypedLLVMAlloca :: (1 <= w, KnownNat w) => TypedReg (LLVMFrameType w) ->
                     LLVMFramePerm w -> Integer ->
                     TypedLLVMStmt w (LLVMPointerType w)
                     (RNil :> LLVMFrameType w)
                     (RNil :> LLVMFrameType w :> LLVMPointerType w)

  -- | Create a new LLVM frame
  --
  -- Type: @. -o ret:frame()@
  TypedLLVMCreateFrame :: (1 <= w, KnownNat w) =>
                          TypedLLVMStmt w (LLVMFrameType w) RNil
                          (RNil :> LLVMFrameType w)

  -- | Delete an LLVM frame and deallocate all memory objects allocated in it,
  -- assuming that the current distinguished permissions @ps@ correspond to the
  -- write permissions to all those objects allocated on the frame
  --
  -- Type: @ps, fp:frame(ps) -o .@
  TypedLLVMDeleteFrame :: (1 <= w, KnownNat w) => TypedReg (LLVMFrameType w) ->
                          LLVMFramePerm w -> DistPerms ps ->
                          TypedLLVMStmt w UnitType (ps :> LLVMFrameType w) RNil

  -- | Typed version of 'LLVM_LoadHandle', that loads the function handle
  -- referred to by a function pointer, assuming we know it has one:
  --
  -- Type: @x:llvm_funptr(fun_perm) -o ret:fun_perm@
  TypedLLVMLoadHandle :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                         FunPerm ghosts (CtxToRList cargs) ret ->
                         TypedLLVMStmt w (FunctionHandleType cargs ret)
                         (RNil :> LLVMPointerType w)
                         (RNil :> FunctionHandleType cargs ret)

  -- | Typed version of 'LLVM_ResolveGlobal', that resolves a 'GlobalSymbol' to
  -- an LLVM value, assuming it has the given permission in the environment:
  --
  -- Type: @. -o ret:p@
  TypedLLVMResolveGlobal :: (1 <= w, KnownNat w) =>
                            GlobalSymbol -> ValuePerm (LLVMPointerType w) ->
                            TypedLLVMStmt w (LLVMPointerType w)
                            RNil (RNil :> LLVMPointerType w)


-- | Return the input permissions for a 'TypedStmt'
typedStmtIn :: TypedStmt ext rets ps_in ps_out -> DistPerms ps_in
typedStmtIn (TypedSetReg _ _) = DistPermsNil
typedStmtIn (TypedSetRegPermExpr _ _) = DistPermsNil
typedStmtIn (TypedCall (TypedReg f) fun_perm ghosts args) =
  DistPermsCons
  (funPermDistIns fun_perm (typedRegsToVars args) ghosts)
  f (ValPerm_Conj1 $ Perm_Fun fun_perm)
typedStmtIn BeginLifetime = DistPermsNil
typedStmtIn (EndLifetime l perms ps end_perms) =
  case permListToDistPerms ps of
    Some perms'
      | Just Refl <- testEquality perms' perms ->
        appendDistPerms
        (DistPermsCons (minLtEndPerms (PExpr_Var l) perms)
         l (ValPerm_Conj [Perm_LOwned ps]))
        end_perms
    _ -> error "typedStmtIn: EndLifetime: malformed arguments"
typedStmtIn (TypedAssert _ _) = DistPermsNil
typedStmtIn (TypedLLVMStmt llvmStmt) = typedLLVMStmtIn llvmStmt

-- | Return the input permissions for a 'TypedLLVMStmt'
typedLLVMStmtIn :: TypedLLVMStmt w ret ps_in ps_out -> DistPerms ps_in
typedLLVMStmtIn (ConstructLLVMWord _) = DistPermsNil
typedLLVMStmtIn (AssertLLVMWord (TypedReg x) e) =
  distPerms1 x (ValPerm_Eq $ PExpr_LLVMWord e)
typedLLVMStmtIn (AssertLLVMPtr (TypedReg x)) =
  distPerms1 x (ValPerm_Conj1 Perm_IsLLVMPtr)
typedLLVMStmtIn (DestructLLVMWord (TypedReg x) e) =
  distPerms1 x (ValPerm_Eq $ PExpr_LLVMWord e)
typedLLVMStmtIn (OffsetLLVMValue _ _) =
  DistPermsNil
typedLLVMStmtIn (TypedLLVMLoad (TypedReg x) fp ps ps_l) =
  permAssert
  (lifetimeCurrentPermsLifetime ps_l == llvmFieldLifetime fp)
  "typedLLVMStmtIn: TypedLLVMLoad: mismatch for field lifetime" $
  permAssert (bvEq (llvmFieldOffset fp) (bvInt 0))
  "typedLLVMStmtIn: TypedLLVMLoad: mismatch for field offset" $
  appendDistPerms
  (DistPermsCons ps x (ValPerm_Conj1 $ Perm_LLVMField fp))
  (lifetimeCurrentPermsPerms ps_l)
typedLLVMStmtIn (TypedLLVMStore (TypedReg x) fp _ ps cur_ps) =
  permAssert (llvmFieldRW fp == PExpr_Write &&
              bvEq (llvmFieldOffset fp) (bvInt 0) &&
              llvmFieldLifetime fp == lifetimeCurrentPermsLifetime cur_ps)
  "typedLLVMStmtIn: TypedLLVMStore: mismatch for field permission" $
  appendDistPerms
  (DistPermsCons ps x (ValPerm_Conj1 $ Perm_LLVMField fp))
  (lifetimeCurrentPermsPerms cur_ps)
typedLLVMStmtIn (TypedLLVMAlloca (TypedReg f) fperms _) =
  distPerms1 f (ValPerm_Conj [Perm_LLVMFrame fperms])
typedLLVMStmtIn TypedLLVMCreateFrame = DistPermsNil
typedLLVMStmtIn (TypedLLVMDeleteFrame (TypedReg f) fperms perms) =
  case llvmFrameDeletionPerms fperms of
    Some perms'
      | Just Refl <- testEquality perms perms' ->
        DistPermsCons perms f (ValPerm_Conj1 $ Perm_LLVMFrame fperms)
    _ -> error "typedLLVMStmtIn: incorrect perms in rule"
typedLLVMStmtIn (TypedLLVMLoadHandle (TypedReg f) fun_perm) =
  distPerms1 f (ValPerm_Conj1 $ Perm_LLVMFunPtr fun_perm)
typedLLVMStmtIn (TypedLLVMResolveGlobal _ _) =
  DistPermsNil

-- | Return the output permissions for a 'TypedStmt'
typedStmtOut :: TypedStmt ext rets ps_in ps_out -> MapRList Name rets ->
                DistPerms ps_out
typedStmtOut (TypedSetReg _ (TypedExpr _ (Just e))) (_ :>: ret) =
  distPerms1 ret (ValPerm_Eq e)
typedStmtOut (TypedSetReg _ (TypedExpr _ Nothing)) (_ :>: ret) =
  distPerms1 ret ValPerm_True
typedStmtOut (TypedSetRegPermExpr _ e) (_ :>: ret) =
  distPerms1 ret (ValPerm_Eq e)
typedStmtOut (TypedCall _ fun_perm ghosts args) (_ :>: ret) =
  funPermDistOuts fun_perm (typedRegsToVars args :>: ret) ghosts
typedStmtOut BeginLifetime (_ :>: l) =
  distPerms1 l $ ValPerm_Conj [Perm_LOwned PExpr_PermListNil]
typedStmtOut (EndLifetime l perms _ _) _ = perms
typedStmtOut (TypedAssert _ _) _ = DistPermsNil
typedStmtOut (TypedLLVMStmt llvmStmt) (_ :>: ret) =
  typedLLVMStmtOut llvmStmt ret

-- | Return the output permissions for a 'TypedStmt'
typedLLVMStmtOut :: TypedLLVMStmt w ret ps_in ps_out -> Name ret ->
                    DistPerms ps_out
typedLLVMStmtOut (ConstructLLVMWord (TypedReg x)) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_LLVMWord $ PExpr_Var x)
typedLLVMStmtOut (AssertLLVMWord (TypedReg x) _) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_Nat 0)
typedLLVMStmtOut (AssertLLVMPtr _) _ = DistPermsNil
typedLLVMStmtOut (DestructLLVMWord (TypedReg x) e) ret =
  distPerms1 ret (ValPerm_Eq e)
typedLLVMStmtOut (OffsetLLVMValue (TypedReg x) off) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_LLVMOffset x off)
typedLLVMStmtOut (TypedLLVMLoad (TypedReg x) fp ps ps_l) ret =
  if lifetimeCurrentPermsLifetime ps_l == llvmFieldLifetime fp then
    appendDistPerms
    (DistPermsCons
     (DistPermsCons ps
      x (ValPerm_Conj1 $ Perm_LLVMField $
         fp { llvmFieldContents = ValPerm_Eq (PExpr_Var ret) }))
     ret (llvmFieldContents fp))
    (lifetimeCurrentPermsPerms ps_l)
  else
    error "typedLLVMStmtOut: TypedLLVMLoad: mismatch for field lifetime"
typedLLVMStmtOut (TypedLLVMStore (TypedReg x) fp e ps cur_ps) _ =
  permAssert (llvmFieldRW fp == PExpr_Write &&
              bvEq (llvmFieldOffset fp) (bvInt 0) &&
              llvmFieldLifetime fp == lifetimeCurrentPermsLifetime cur_ps)
  "typedLLVMStmtOut: TypedLLVMStore: mismatch for field permission" $
  appendDistPerms
  (DistPermsCons ps x (ValPerm_Conj1 $ Perm_LLVMField $
                       fp { llvmFieldContents = ValPerm_Eq e }))
  (lifetimeCurrentPermsPerms cur_ps)
typedLLVMStmtOut (TypedLLVMAlloca
                  (TypedReg f) (fperms :: LLVMFramePerm w) len) ret =
  distPerms2 f (ValPerm_Conj [Perm_LLVMFrame ((PExpr_Var ret, len):fperms)])
  ret (llvmFieldsPermOfSize Proxy len)
typedLLVMStmtOut TypedLLVMCreateFrame ret =
  distPerms1 ret $ ValPerm_Conj [Perm_LLVMFrame []]
typedLLVMStmtOut (TypedLLVMDeleteFrame _ _ _) _ = DistPermsNil
typedLLVMStmtOut (TypedLLVMLoadHandle _ fun_perm) ret =
  distPerms1 ret (ValPerm_Conj1 $ Perm_Fun fun_perm)
typedLLVMStmtOut (TypedLLVMResolveGlobal _ p) ret =
  distPerms1 ret p


-- | Check that the permission stack of the given permission set matches the
-- input permissions of the given statement, and replace them with the output
-- permissions of the statement
applyTypedStmt :: TypedStmt ext rets ps_in ps_out -> MapRList Name rets ->
                  PermSet ps_in -> PermSet ps_out
applyTypedStmt stmt rets =
  modifyDistPerms $ \perms ->
  if perms == typedStmtIn stmt then
    typedStmtOut stmt rets
  else
    error "applyTypedStmt: unexpected input permissions!"


----------------------------------------------------------------------
-- * Typed Sequences of Crucible Statements
----------------------------------------------------------------------

-- | Typed return argument
data TypedRet tops ret ps =
  TypedRet
  (ps :~: tops :> ret) (TypeRepr ret) (TypedReg ret)
  (Binding ret (DistPerms ps))


-- | Typed Crucible block termination statements
data TypedTermStmt blocks tops ret ps_in where
  -- | Jump to the given jump target
  TypedJump :: PermImpl (TypedJumpTarget blocks tops) ps_in ->
               TypedTermStmt blocks tops ret ps_in

  -- | Branch on condition: if true, jump to the first jump target, and
  -- otherwise jump to the second jump target
  TypedBr :: TypedReg BoolType ->
             PermImpl (TypedJumpTarget blocks tops) ps_in ->
             PermImpl (TypedJumpTarget blocks tops) ps_in ->
             TypedTermStmt blocks tops ret ps_in

  -- | Return from function, providing the return value and also proof that the
  -- current permissions imply the required return permissions
  TypedReturn :: PermImpl (TypedRet tops ret) ps_in ->
                 TypedTermStmt blocks tops ret ps_in

  -- | Block ends with an error
  TypedErrorStmt :: TypedReg StringType -> TypedTermStmt blocks tops ret ps_in


-- | A typed sequence of Crucible statements
data TypedStmtSeq ext blocks tops ret ps_in where
  -- | A permission implication step, which modifies the current permission
  -- set. This can include pattern-matches and/or assertion failures.
  TypedImplStmt :: PermImpl (TypedStmtSeq ext blocks tops ret) ps_in ->
                   TypedStmtSeq ext blocks tops ret ps_in

  -- | Typed version of 'ConsStmt', which binds new variables for the return
  -- value(s) of each statement
  TypedConsStmt :: ProgramLoc ->
                   TypedStmt ext rets ps_in ps_next ->
                   Mb rets (TypedStmtSeq ext blocks tops ret ps_next) ->
                   TypedStmtSeq ext blocks tops ret ps_in

  -- | Typed version of 'TermStmt', which terminates the current block
  TypedTermStmt :: ProgramLoc ->
                   TypedTermStmt blocks tops ret ps_in ->
                   TypedStmtSeq ext blocks tops ret ps_in


$(mkNuMatching [t| forall w tp ps_out ps_in.
                TypedLLVMStmt w tp ps_out ps_in |])
$(mkNuMatching [t| forall ext rets ps_in ps_out. NuMatchingExtC ext =>
                TypedStmt ext rets ps_in ps_out |])
$(mkNuMatching [t| forall tops ret ps. TypedRet tops ret ps |])

instance NuMatchingAny1 (TypedRet tops ret) where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall blocks tops ret ps_in.
                TypedTermStmt blocks tops ret ps_in |])
$(mkNuMatching [t| forall ext blocks tops ret ps_in.
                NuMatchingExtC ext => TypedStmtSeq ext blocks tops ret ps_in |])

instance NuMatchingExtC ext =>
         NuMatchingAny1 (TypedStmtSeq ext blocks tops ret) where
  nuMatchingAny1Proof = nuMatchingProof


instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedReg tp) m where
  genSubst s [nuP| TypedReg x |] = TypedReg <$> genSubst s x

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (RegWithVal tp) m where
  genSubst s [nuP| RegWithVal r e |] =
    RegWithVal <$> genSubst s r <*> genSubst s e
  genSubst s [nuP| RegNoVal r |] = RegNoVal <$> genSubst s r

instance SubstVar PermVarSubst m =>
         Substable1 PermVarSubst RegWithVal m where
  genSubst1 = genSubst

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedRegs tp) m where
  genSubst _ [nuP| TypedRegsNil |] = return TypedRegsNil
  genSubst s [nuP| TypedRegsCons rs r |] =
    TypedRegsCons <$> genSubst s rs <*> genSubst s r

instance (PermCheckExtC ext, NuMatchingAny1 f,
          NuMatching (AssertionClassifier ext f),
          SubstVar PermVarSubst m, Substable1 PermVarSubst f m,
          Substable PermVarSubst (f BoolType) m) =>
         Substable PermVarSubst (App ext f a) m where
  genSubst s [nuP| BaseIsEq tp e1 e2 |] =
    BaseIsEq (mbLift tp) <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| EmptyApp |] = return EmptyApp
  genSubst s [nuP| BoolLit b |] = return $ BoolLit $ mbLift b
  genSubst s [nuP| Not e |] =
    Not <$> genSubst1 s e
  genSubst s [nuP| And e1 e2 |] =
    And <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| Or e1 e2 |] =
    Or <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BoolXor e1 e2 |] =
    BoolXor <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| NatLit n |] =
    return $ NatLit $ mbLift n
  genSubst s [nuP| NatLt e1 e2 |] =
    NatLt <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| NatLe e1 e2 |] =
    NatLe <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| NatAdd e1 e2 |] =
    NatAdd <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| NatSub e1 e2 |] =
    NatSub <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| NatMul e1 e2 |] =
    NatMul <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| NatDiv e1 e2 |] =
    NatDiv <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| NatMod e1 e2 |] =
    NatMod <$> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| HandleLit h |] =
    return $ HandleLit $ mbLift h
  genSubst s mb_e@[nuP| WithAssertion tp (PartialExp p e) |] =
    let getExtRepr :: PermCheckExtC ext => Mb ctx (App ext f a) -> ExtRepr ext
        getExtRepr _ = knownRepr in
    case getExtRepr mb_e of
      ExtRepr_Unit ->
        WithAssertion (mbLift tp) <$>
        (PartialExp <$> genSubst s p <*> genSubst1 s e)
      ExtRepr_LLVM ->
        WithAssertion (mbLift tp) <$>
        (PartialExp <$> genSubst s p <*> genSubst1 s e)
  genSubst s [nuP| BVLit w i |] =
    BVLit <$> genSubst s w <*> return (mbLift i)
  genSubst s [nuP| BVConcat w1 w2 e1 e2 |] =
    BVConcat <$> genSubst s w1 <*> genSubst s w2 <*>
    genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVTrunc w1 w2 e |] =
    BVTrunc <$> genSubst s w1 <*> genSubst s w2 <*> genSubst1 s e
  genSubst s [nuP| BVZext w1 w2 e |] =
    BVZext <$> genSubst s w1 <*> genSubst s w2 <*> genSubst1 s e
  genSubst s [nuP| BVSext w1 w2 e |] =
    BVSext <$> genSubst s w1 <*> genSubst s w2 <*> genSubst1 s e
  genSubst s [nuP| BVNot w e |] =
    BVNot <$> genSubst s w <*> genSubst1 s e
  genSubst s [nuP| BVAnd w e1 e2 |] =
    BVAnd <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVOr w e1 e2 |] =
    BVOr <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVXor w e1 e2 |] =
    BVXor <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVNeg w e |] =
    BVNeg <$> genSubst s w <*> genSubst1 s e
  genSubst s [nuP| BVAdd w e1 e2 |] =
    BVAdd <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVSub w e1 e2 |] =
    BVSub <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVMul w e1 e2 |] =
    BVMul <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVUdiv w e1 e2 |] =
    BVUdiv <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVSdiv w e1 e2 |] =
    BVSdiv <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVUrem w e1 e2 |] =
    BVUrem <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVSrem w e1 e2 |] =
    BVSrem <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVUle w e1 e2 |] =
    BVUle <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVUlt w e1 e2 |] =
    BVUlt <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVSle w e1 e2 |] =
    BVSle <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVSlt w e1 e2 |] =
    BVSlt <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVCarry w e1 e2 |] =
    BVSlt <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BVSCarry w e1 e2 |] =
    BVSlt <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
  genSubst s [nuP| BoolToBV w e |] =
    BoolToBV <$> genSubst s w <*> genSubst1 s e
  genSubst s [nuP| BVNonzero w e |] =
    BVNonzero <$> genSubst s w <*> genSubst1 s e
  genSubst _ [nuP| TextLit text |] =
    return $ TextLit $ mbLift text
  genSubst _ mb_expr =
    error ("genSubst: unhandled Crucible expression construct: "
           ++ mbLift (fmap (show . ppApp (const (string "_"))) mb_expr))

instance (NuMatchingAny1 f, SubstVar PermVarSubst m,
          Substable1 PermVarSubst f m) =>
         Substable PermVarSubst (LLVMSafetyAssertion f) m where
  genSubst s [nuP| LLVMSafetyAssertion bbeh p extra |] =
    LLVMSafetyAssertion (mbLift bbeh) <$> genSubst1 s p <*> return (mbLift extra)

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (NoAssertionClassifier f) m where
  genSubst _ _ = error "Unreachable!"

instance (NuMatching a, Substable s a m) => Substable s (NonEmpty a) m where
  genSubst s [nuP| x :| xs |] = (:|) <$> genSubst s x <*> genSubst s xs

instance (NuMatching a, NuMatching c,
          SubstVar s m, Substable s c m, Substable s a m) =>
         Substable s (AT.AssertionTree c a) m where
  genSubst s [nuP| AT.Leaf a |] = AT.Leaf <$> genSubst s a
  genSubst s [nuP| AT.And ts |] = AT.And <$> genSubst s ts
  genSubst s [nuP| AT.Or ts |] = AT.Or <$> genSubst s ts
  genSubst s [nuP| AT.Ite c t1 t2 |] =
    AT.Ite <$> genSubst s c <*> genSubst s t1 <*> genSubst s t2


instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable PermVarSubst (TypedExpr ext tp) m where
  genSubst s [nuP| TypedExpr app maybe_val |] =
    TypedExpr <$> genSubst s app <*> genSubst s maybe_val

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedLLVMStmt w tp ps_out ps_in) m where
  genSubst s [nuP| ConstructLLVMWord r |] = ConstructLLVMWord <$> genSubst s r
  genSubst s [nuP| AssertLLVMWord r e |] =
    AssertLLVMWord <$> genSubst s r <*> genSubst s e
  genSubst s [nuP| AssertLLVMPtr r |] =
    AssertLLVMPtr <$> genSubst s r
  genSubst s [nuP| DestructLLVMWord r e |] =
    DestructLLVMWord <$> genSubst s r <*> genSubst s e
  genSubst s [nuP| OffsetLLVMValue r off |] =
    OffsetLLVMValue <$> genSubst s r <*> genSubst s off
  genSubst s [nuP| TypedLLVMLoad r fp ps ps_l |] =
    TypedLLVMLoad <$> genSubst s r <*> genSubst s fp <*> genSubst s ps <*>
    genSubst s ps_l
  genSubst s [nuP| TypedLLVMStore r fp e ps cur_ps |] =
    TypedLLVMStore <$> genSubst s r <*> genSubst s fp <*> genSubst s e <*>
    genSubst s ps <*> genSubst s cur_ps
  genSubst s [nuP| TypedLLVMAlloca r fperms i |] =
    TypedLLVMAlloca <$> genSubst s r <*> genSubst s fperms <*>
    return (mbLift i)
  genSubst _ [nuP| TypedLLVMCreateFrame |] = return TypedLLVMCreateFrame
  genSubst s [nuP| TypedLLVMDeleteFrame r fperms perms |] =
    TypedLLVMDeleteFrame <$> genSubst s r <*> genSubst s fperms <*>
    genSubst s perms
  genSubst s [nuP| TypedLLVMLoadHandle r fun_perm |] =
    TypedLLVMLoadHandle <$> genSubst s r <*> genSubst s fun_perm
  genSubst s [nuP| TypedLLVMResolveGlobal gsym p |] =
    TypedLLVMResolveGlobal (mbLift gsym) <$> genSubst s p


instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable PermVarSubst (TypedStmt ext rets ps_in ps_out) m where
  genSubst s [nuP| TypedSetReg tp expr |] =
    TypedSetReg (mbLift tp) <$> genSubst s expr
  genSubst s [nuP| TypedSetRegPermExpr tp expr |] =
    TypedSetRegPermExpr (mbLift tp) <$> genSubst s expr
  genSubst s [nuP| TypedCall f fun_perm ghosts args |] =
    TypedCall <$> genSubst s f <*> genSubst s fun_perm <*>
    genSubst s ghosts <*> genSubst s args
  genSubst s [nuP| BeginLifetime |] = return BeginLifetime
  genSubst s [nuP| EndLifetime l perms ps end_perms |] =
    EndLifetime <$> genSubst s l <*> genSubst s perms <*> genSubst s ps <*>
    genSubst s end_perms
  genSubst s [nuP| TypedAssert r1 r2 |] =
    TypedAssert <$> genSubst s r1 <*> genSubst s r2
  genSubst s [nuP| TypedLLVMStmt llvmStmt |] =
    TypedLLVMStmt <$> genSubst s llvmStmt


instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedRet tops ret ps) m where
  genSubst s [nuP| TypedRet e tp ret mb_perms |] =
    TypedRet (mbLift e) (mbLift tp) <$> genSubst s ret <*> genSubst s mb_perms

instance SubstVar PermVarSubst m =>
         Substable1 PermVarSubst (TypedRet tops ret) m where
  genSubst1 = genSubst

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedJumpTarget blocks tops ps) m where
  genSubst s [nuP| TypedJumpTarget entryID prx ctx perms |] =
    TypedJumpTarget (mbLift entryID) (mbLift prx) (mbLift ctx) <$>
    genSubst s perms

instance SubstVar PermVarSubst m =>
         Substable1 PermVarSubst (TypedJumpTarget blocks tops) m where
  genSubst1 = genSubst

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedTermStmt blocks tops ret ps_in) m where
  genSubst s [nuP| TypedJump impl_tgt |] = TypedJump <$> genSubst s impl_tgt
  genSubst s [nuP| TypedBr reg impl_tgt1 impl_tgt2 |] =
    TypedBr <$> genSubst s reg <*> genSubst s impl_tgt1 <*>
    genSubst s impl_tgt2
  genSubst s [nuP| TypedReturn impl_ret |] =
    TypedReturn <$> genSubst s impl_ret
  genSubst s [nuP| TypedErrorStmt r |] = TypedErrorStmt <$> genSubst s r

instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable PermVarSubst (TypedStmtSeq ext blocks tops ret ps_in) m where
  genSubst s [nuP| TypedImplStmt impl_seq |] =
    TypedImplStmt <$> genSubst s impl_seq
  genSubst s [nuP| TypedConsStmt loc stmt mb_seq |] =
    TypedConsStmt (mbLift loc) <$> genSubst s stmt <*> genSubst s mb_seq
  genSubst s [nuP| TypedTermStmt loc term_stmt |] =
    TypedTermStmt (mbLift loc) <$> genSubst s term_stmt

instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable1 PermVarSubst (TypedStmtSeq ext blocks tops ret) m where
  genSubst1 = genSubst


----------------------------------------------------------------------
-- * Typed Control-Flow Graphs
----------------------------------------------------------------------

-- | A single, typed entrypoint to a Crucible block. Note that our blocks
-- implicitly take extra "ghost" arguments, that are needed to express the input
-- and output permissions. The first of these ghost arguments are the top-level
-- inputs to the entire function. Each entrypoint is also marked with a 'Bool'
-- flag that indicates whether it is the head of a strongly-connected component,
-- i.e., if it is the entrypoint of a loop.
--
-- FIXME: add a @ghostss@ type argument that associates a @ghosts@ type with
-- each index of each block, rather than having @ghost@ existentially bound
-- here.
data TypedEntry ext blocks tops ret args where
  TypedEntry ::
    !(TypedEntryID blocks args ghosts) ->
    !(CruCtx tops) -> !(CruCtx args) -> !(TypeRepr ret) ->
    !Bool -> !(MbValuePerms ((tops :++: args) :++: ghosts)) ->
    !(Mb ((tops :++: args) :++: ghosts :> ret) (ValuePerms (tops :> ret))) ->
    !(Mb ((tops :++: args) :++: ghosts)
      (TypedStmtSeq ext blocks tops ret ((tops :++: args) :++: ghosts))) ->
    TypedEntry ext blocks tops ret args

typedEntryIndex :: TypedEntry ext blocks tops ret args -> Int
typedEntryIndex (TypedEntry entryID _ _ _ _ _ _ _) = entryIndex entryID

typedEntryIsSCC :: TypedEntry ext blocks tops ret args -> Bool
typedEntryIsSCC (TypedEntry _ _ _ _ is_scc _ _ _) = is_scc

-- | Get the body of a 'TypedEntry' using its 'TypedEntryID' to indicate the
-- @ghosts@ argument. It is an error if the wrong 'TypedEntryID' is given.
typedEntryBody :: TypedEntryID blocks args ghosts ->
                  TypedEntry ext blocks tops ret args ->
                  Mb ((tops :++: args) :++: ghosts)
                  (TypedStmtSeq ext blocks tops ret
                   ((tops :++: args) :++: ghosts))
typedEntryBody entryID (TypedEntry entryID' _ _ _ _ _ _ body)
  | Just Refl <- testEquality entryID entryID' = body
typedEntryBody _ _ = error "typedEntryBody"


-- | A typed Crucible block is a list of typed entrypoints to that block
newtype TypedBlock ext blocks tops ret args
  = TypedBlock [TypedEntry ext blocks tops ret args]

-- | A map assigning a 'TypedBlock' to each 'BlockID'
type TypedBlockMap ext blocks tops ret =
  MapRList (TypedBlock ext blocks tops ret) blocks

instance Show (TypedEntry ext blocks tops ret args) where
  show (TypedEntry entryID _ _ _ _ _ _ _) =
    "<entry " ++ show (entryIDIndices entryID) ++ ">"

instance Show (TypedBlock ext blocks tops ret args) where
  show (TypedBlock entries) = show entries

instance Show (TypedBlockMap ext blocks tops ret) where
  show blkMap =
    show $ mapRListToList $ mapMapRList (Constant . show) blkMap

-- | A typed Crucible CFG
data TypedCFG
     (ext :: Type)
     (blocks :: RList (RList CrucibleType))
     (ghosts :: RList CrucibleType)
     (inits :: RList CrucibleType)
     (ret :: CrucibleType)
  = TypedCFG { tpcfgHandle :: !(TypedFnHandle ghosts inits ret)
             , tpcfgFunPerm :: !(FunPerm ghosts inits ret)
             , tpcfgBlockMap ::
                 !(TypedBlockMap ext blocks (ghosts :++: inits) ret)
             , tpcfgEntryBlockID ::
                 !(TypedEntryID blocks inits RNil)
             }


tpcfgInputPerms :: TypedCFG ext blocks ghosts inits ret ->
                   Mb ghosts (MbValuePerms inits)
tpcfgInputPerms = funPermIns . tpcfgFunPerm

tpcfgOutputPerms :: TypedCFG ext blocks ghosts inits ret ->
                    Mb ghosts (MbValuePerms (inits :> ret))
tpcfgOutputPerms = funPermOuts . tpcfgFunPerm


----------------------------------------------------------------------
-- * Monad(s) for Permission Checking
----------------------------------------------------------------------

-- | A translation of a Crucible context to 'TypedReg's that exist in the local
-- Hobbits context
type CtxTrans ctx = Assignment TypedReg ctx

-- | Build a Crucible context translation from a set of variables
mkCtxTrans :: Assignment f ctx -> MapRList Name (CtxToRList ctx) -> CtxTrans ctx
mkCtxTrans (viewAssign -> AssignEmpty) _ = Ctx.empty
mkCtxTrans (viewAssign -> AssignExtend ctx' _) (ns :>: n) =
  extend (mkCtxTrans ctx' ns) (TypedReg n)

-- | Add a variable to the current Crucible context translation
addCtxName :: CtxTrans ctx -> ExprVar tp -> CtxTrans (ctx ::> tp)
addCtxName ctx x = extend ctx (TypedReg x)

-- | GADT telling us that @ext@ is a syntax extension we can handle
data ExtRepr ext where
  ExtRepr_Unit :: ExtRepr ()
  ExtRepr_LLVM :: (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) =>
                  ExtRepr (LLVM arch)

instance KnownRepr ExtRepr () where
  knownRepr = ExtRepr_Unit

instance (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) =>
         KnownRepr ExtRepr (LLVM arch) where
  knownRepr = ExtRepr_LLVM

-- | The constraints for a Crucible syntax extension that supports permission
-- checking
type PermCheckExtC ext =
  (NuMatchingExtC ext, IsSyntaxExtension ext, KnownRepr ExtRepr ext)

-- | Extension-specific state
data PermCheckExtState ext where
  -- | No extension-specific state for the empty extension
  PermCheckExtState_Unit :: PermCheckExtState ()

  -- | The extension-specific state for LLVM is the current frame pointer, if it
  -- exists
  PermCheckExtState_LLVM :: Maybe (TypedReg (LLVMFrameType (ArchWidth arch))) ->
                            PermCheckExtState (LLVM arch)

-- | Create a default empty extension-specific state object
emptyPermCheckExtState :: ExtRepr ext -> PermCheckExtState ext
emptyPermCheckExtState ExtRepr_Unit = PermCheckExtState_Unit
emptyPermCheckExtState ExtRepr_LLVM = PermCheckExtState_LLVM Nothing

-- | Get all the names contained in a 'PermCheckExtState'
permCheckExtStateNames :: PermCheckExtState ext -> Some (MapRList ExprVar)
permCheckExtStateNames (PermCheckExtState_LLVM (Just treg)) =
  Some (MNil :>: typedRegVar treg)
permCheckExtStateNames (PermCheckExtState_LLVM Nothing) = Some MNil
permCheckExtStateNames (PermCheckExtState_Unit) = Some MNil

-- | The local state maintained while type-checking is the current permission
-- set and the permissions required on return from the entire function.
data PermCheckState ext tops ret ps =
  PermCheckState
  {
    stCurPerms :: PermSet ps,
    stExtState :: PermCheckExtState ext,
    stTopVars  :: MapRList Name tops,
    stVarTypes :: NameMap TypeRepr,
    stPPInfo   :: PPInfo
  }

-- | Like the 'set' method of a lens, but allows the @ps@ argument to change
setSTCurPerms :: PermSet ps2 -> PermCheckState ext tops ret ps1 ->
                 PermCheckState ext tops ret ps2
setSTCurPerms perms (PermCheckState {..}) =
  PermCheckState { stCurPerms = perms, .. }

modifySTCurPerms :: (PermSet ps1 -> PermSet ps2) ->
                    PermCheckState ext tops ret ps1 ->
                    PermCheckState ext tops ret ps2
modifySTCurPerms f_perms st = setSTCurPerms (f_perms $ stCurPerms st) st

-- | The information needed to type-check a single entrypoint of a block
data BlockEntryInfo blocks tops ret args where
  BlockEntryInfo :: {
    entryInfoID :: TypedEntryID blocks args ghosts,
    entryInfoTops :: CruCtx tops,
    entryInfoArgs :: CruCtx args,
    entryInfoPermsIn :: MbValuePerms ((tops :++: args) :++: ghosts)
  } -> BlockEntryInfo blocks tops ret args

-- | Extract the 'BlockID' from entrypoint info
entryInfoBlockID :: BlockEntryInfo blocks tops ret args -> Member blocks args
entryInfoBlockID (BlockEntryInfo entryID _ _ _) = entryBlockID entryID

-- | Extract the entry id from entrypoint info
entryInfoIndex :: BlockEntryInfo blocks tops ret args -> Int
entryInfoIndex (BlockEntryInfo entryID _ _ _) = entryIndex entryID

-- | Extract the block id, entry id pair from a 'BlockEntryInfo"
entryInfoIndices :: BlockEntryInfo blocks tops ret args -> (Int, Int)
entryInfoIndices (BlockEntryInfo entryID _ _ _) = entryIDIndices entryID

-- | Information about the current state of type-checking for a block
data BlockInfo ext blocks tops ret args =
  BlockInfo
  {
    blockInfoMember :: Member blocks args,
    blockInfoEntries :: [BlockEntryInfo blocks tops ret args],
    blockInfoBlock :: Maybe (TypedBlock ext blocks tops ret args)
  }

-- | Test if a block has been type-checked yet, which is true iff its
-- translation has been stored in its info yet
blockInfoVisited :: BlockInfo ext blocks tops ret args -> Bool
blockInfoVisited (BlockInfo { blockInfoBlock = Just _ }) = True
blockInfoVisited _ = False

{- FIXME: remove?
-- | Add a new 'BlockEntryInfo' to a 'BlockInfo' and return its 'TypedEntryID'.
-- This assumes that the block has not been visited; if it has, it is an error.
blockInfoAddEntry :: CruCtx tops -> CruCtx args -> CruCtx ghosts ->
                     MbDistPerms ((tops :++: args) :++: ghosts) ->
                     BlockInfo ext blocks tops ret args ->
                     (BlockInfo ext blocks tops ret args,
                      TypedEntryID blocks args ghosts)
blockInfoAddEntry tops args ghosts perms_in info =
  if blockInfoVisited info then error "blockInfoAddEntry" else
    let entries = blockInfoEntries info
        entryID = TypedEntryID (blockInfoMember info) ghosts (length entries) in
    (info { blockInfoEntries =
              entries ++ [BlockEntryInfo entryID tops args perms_in] },
     entryID)
-}

type BlockInfoMap ext blocks tops ret =
  MapRList (BlockInfo ext blocks tops ret) blocks

blockInfoMapIxs :: BlockInfoMap ext blocks tops ret -> [(Int,Int)]
blockInfoMapIxs =
  concat . mapRListToList . mapMapRList
  (Constant . map entryInfoIndices . blockInfoEntries)


-- | Build an empty 'BlockInfoMap' from an assignment
emptyBlockInfoMap :: Assignment f blocks ->
                     BlockInfoMap ext (CtxCtxToRList blocks) tops ret
emptyBlockInfoMap asgn =
  mapMapRList (\memb -> BlockInfo memb [] Nothing) (helper asgn)
  where
    helper :: Assignment f ctx ->
              MapRList (Member (CtxCtxToRList ctx)) (CtxCtxToRList ctx)
    helper (viewAssign -> AssignEmpty) = MNil
    helper (viewAssign -> AssignExtend asgn _) =
      mapMapRList Member_Step (helper asgn) :>: Member_Base

{- FIXME: remove?
-- | Add a new 'BlockEntryInfo' to a block info map, returning the newly updated
-- map and the new 'TypedEntryID'. This assumes that the block has not been
-- visited; if it has, it is an error.
blockInfoMapAddEntry :: Member blocks args ->
                        CruCtx tops -> CruCtx args -> CruCtx ghosts ->
                        MbDistPerms ((tops :++: args) :++: ghosts) ->
                        BlockInfoMap ext blocks tops ret ->
                        (BlockInfoMap ext blocks tops ret,
                         TypedEntryID blocks args ghosts)
blockInfoMapAddEntry memb tops args ghosts perms_in blkMap =
  let blkInfo = mapRListLookup memb blkMap
      (blkInfo', entryID) =
        blockInfoAddEntry tops args ghosts perms_in blkInfo in
  (mapRListSet memb blkInfo' blkMap, entryID)
-}

-- | Set the 'TypedBlock' for a given block id, thereby marking it as
-- visited. It is an error if it is already set.
blockInfoMapSetBlock :: Member blocks args ->
                        TypedBlock ext blocks tops ret args ->
                        BlockInfoMap ext blocks tops ret ->
                        BlockInfoMap ext blocks tops ret
blockInfoMapSetBlock memb blk =
  mapRListModify memb $ \info ->
  if blockInfoVisited info then
    error "blockInfoMapSetBlock: block already set"
  else
    info { blockInfoBlock = Just blk }


-- | The translation of a Crucible block id
newtype BlockIDTrans blocks args =
  BlockIDTrans { unBlockIDTrans :: Member blocks (CtxToRList args) }

extendBlockIDTrans :: BlockIDTrans blocks args ->
                      BlockIDTrans (blocks :> tp) args
extendBlockIDTrans (BlockIDTrans memb) = BlockIDTrans $ Member_Step memb

-- | Build a map from Crucible block IDs to 'Member' proofs
buildBlockIDMap :: Assignment f cblocks ->
                   Assignment (BlockIDTrans (CtxCtxToRList cblocks)) cblocks
buildBlockIDMap (viewAssign -> AssignEmpty) = Ctx.empty
buildBlockIDMap (viewAssign -> AssignExtend asgn _) =
  Ctx.extend (fmapFC extendBlockIDTrans $ buildBlockIDMap asgn)
  (BlockIDTrans Member_Base)

-- | Top-level state, maintained outside of permission-checking single blocks
data TopPermCheckState ext cblocks blocks tops ret =
  TopPermCheckState
  {
    stTopCtx :: CruCtx tops,
    stRetType :: TypeRepr ret,
    stRetPerms :: MbValuePerms (tops :> ret),
    stBlockTrans :: Assignment (BlockIDTrans blocks) cblocks,
    stBlockInfo :: BlockInfoMap ext blocks tops ret,
    stPermEnv :: PermEnv
  }

{-
$(mkNuMatching [t| forall ext cblocks blocks ret.
                TopPermCheckState ext cblocks blocks ret |])

instance Closable (TopPermCheckState ext cblocks blocks ret) where
  toClosed (TopPermCheckState {..}) =
    $(mkClosed [| TopPermCheckState |])
    `clApply` (toClosed stRetType)
    `clApplyCl` stBlockTrans
    `clApplyCl` stBlockInfo
    `clApplyCl` stFunTypeEnv

instance BindState (TopPermCheckState ext cblocks blocks ret) where
  bindState [nuP| TopPermCheckState retType bt i env |] =
    TopPermCheckState (mbLift retType) (mbLift bt) (mbLift i) (mbLift env)
-}

-- | Build an empty 'TopPermCheckState' from a Crucible 'BlockMap'
emptyTopPermCheckState ::
  CruCtx tops -> TypeRepr ret -> MbValuePerms (tops :> ret) ->
  BlockMap ext cblocks ret -> PermEnv ->
  TopPermCheckState ext cblocks (CtxCtxToRList cblocks) tops ret
emptyTopPermCheckState tops ret retPerms blkMap env =
  TopPermCheckState { stTopCtx = tops
                    , stRetType = ret
                    , stRetPerms = retPerms
                    , stBlockTrans = buildBlockIDMap blkMap
                    , stBlockInfo = emptyBlockInfoMap blkMap
                    , stPermEnv = env }


-- | Look up a Crucible block id in a top-level perm-checking state
stLookupBlockID :: BlockID cblocks args ->
                   TopPermCheckState ext cblocks blocks tops ret ->
                   Member blocks (CtxToRList args)
stLookupBlockID (BlockID ix) st =
  unBlockIDTrans $ stBlockTrans st Ctx.! ix

-- | The top-level monad for permission-checking CFGs
type TopPermCheckM ext cblocks blocks tops ret =
  State (TopPermCheckState ext cblocks blocks tops ret)

modifyBlockInfo :: (BlockInfoMap ext blocks tops ret ->
                    BlockInfoMap ext blocks tops ret) ->
                   TopPermCheckM ext cblocks blocks tops ret ()
modifyBlockInfo f =
  modify (\st -> st { stBlockInfo = f (stBlockInfo st) })

{-
-- | A datakind for the type-level parameters needed to define blocks, including
-- the @ext@, @blocks@, @ret@ and @args@ arguments
data BlkParams =
  BlkParams Type (RList (RList CrucibleType)) CrucibleType (RList CrucibleType)

type family BlkExt (args :: BlkParams) :: Type where
  BlkExt ('BlkParams ext _ _ _) = ext

type family BlkBlocks (args :: BlkParams) :: (RList (RList CrucibleType)) where
  BlkBlocks ('BlkParams _ blocks _ _) = blocks

type family BlkRet (args :: BlkParams) :: CrucibleType where
  BlkRet ('BlkParams _ _ ret _) = ret

type family BlkArgs (args :: BlkParams) :: RList CrucibleType where
  BlkArgs ('BlkParams _ _ _ args) = args
-}

-- | A change to a 'BlockInfoMap' gives a new entrypoint via a 'BlockEntryInfo'
data BlockInfoMapDelta blocks tops ret where
  BlockInfoMapDelta :: Member blocks args -> BlockEntryInfo blocks tops ret args ->
                       BlockInfoMapDelta blocks tops ret

-- | Get all the 'BlockEntryInfo's for a specific block out of a list of
-- 'BlockInfoMapDelta's
getDeltaEntriesForBlock :: Member blocks args ->
                           [BlockInfoMapDelta blocks tops ret] ->
                           [BlockEntryInfo blocks tops ret args]
getDeltaEntriesForBlock memb =
  mapMaybe (\delta -> case delta of
               BlockInfoMapDelta memb' entry
                 | Just Refl <- testEquality memb memb' ->
                     Just entry
               _ -> Nothing)

-- | Add a new entrypoint to a 'BlockInfoMap'
addBlockEntry :: Member blocks args -> BlockEntryInfo blocks tops ret args ->
                 BlockInfoMap ext blocks tops ret ->
                 BlockInfoMap ext blocks tops ret
addBlockEntry memb entry =
  mapRListModify memb $ \info ->
  info { blockInfoEntries = blockInfoEntries info ++ [entry] }

-- | Apply a 'BlockInfoMapDelta' to a 'BlockInfoMap'
applyBlockInfoMapDelta :: BlockInfoMapDelta blocks tops ret ->
                          BlockInfoMap ext blocks tops ret ->
                          BlockInfoMap ext blocks tops ret
applyBlockInfoMapDelta (BlockInfoMapDelta memb entry) =
  addBlockEntry memb entry

-- | The state that can be modified by "inner" computations. Note that the
-- 'blockInfoBlock' field of any 'BlockInfo's will be ignored.
data InnerPermCheckState blocks tops ret =
  InnerPermCheckState
  {
    innerBlockInfo :: [BlockInfoMapDelta blocks tops ret]
  }

-- | Build an empty, closed 'InnerPermCheckState'
clEmptyInnerPermCheckState ::
  Closed (InnerPermCheckState blocks tops ret)
clEmptyInnerPermCheckState = $(mkClosed [| InnerPermCheckState [] |])


-- | The "inner" monad that runs inside 'PermCheckM' continuations. It can see
-- but not modify the top-level state, but it can add new block entrypoints to
-- be type-checked later
type InnerPermCheckM ext cblocks blocks tops ret =
  ReaderT (TopPermCheckState ext cblocks blocks tops ret)
  (State (Closed (InnerPermCheckState blocks tops ret)))

-- | The generalized monad for permission-checking
type PermCheckM ext cblocks blocks tops ret r1 ps1 r2 ps2 =
  GenStateContM (PermCheckState ext tops ret ps1)
  (InnerPermCheckM ext cblocks blocks tops ret r1)
  (PermCheckState ext tops ret ps2)
  (InnerPermCheckM ext cblocks blocks tops ret r2)

-- | The generalized monad for permission-checking statements
type StmtPermCheckM ext cblocks blocks tops ret ps1 ps2 =
  PermCheckM ext cblocks blocks tops ret
   (TypedStmtSeq ext blocks tops ret ps1) ps1
   (TypedStmtSeq ext blocks tops ret ps2) ps2

liftPermCheckM :: InnerPermCheckM ext cblocks blocks tops ret a ->
                  PermCheckM ext cblocks blocks tops ret r ps r ps a
liftPermCheckM m = gcaptureCC $ \k -> m >>= k

runPermCheckM :: KnownRepr ExtRepr ext =>
                 MapRList Name tops -> PermSet ps_in ->
                 PermCheckM ext cblocks blocks tops ret () ps_out r ps_in () ->
                 InnerPermCheckM ext cblocks blocks tops ret r
runPermCheckM topVars perms m =
  do top_st <- ask
     let st = PermCheckState {
           stCurPerms = perms,
           stExtState = emptyPermCheckExtState knownRepr,
           stTopVars  = topVars,
           stVarTypes = NameMap.empty,
           stPPInfo   = emptyPPInfo }
     runGenContM (runGenStateT m st) (\((), _) -> return ())

-- | Lift an 'InnerPermCheckM' to a 'TopPermCheckM'
liftInnerToTopM :: InnerPermCheckM ext cblocks blocks tops ret a ->
                   TopPermCheckM ext cblocks blocks tops ret a
liftInnerToTopM m =
  do st <- get
     let (a, cl_inner_st) =
           runState (runReaderT m st) clEmptyInnerPermCheckState
     let blockInfoDeltas = innerBlockInfo $ unClosed cl_inner_st
     modify (\top_st' ->
              top_st' { stBlockInfo =
                          foldr applyBlockInfoMapDelta (stBlockInfo top_st')
                          blockInfoDeltas })
     return a

-- | Get the current top-level state
top_get :: PermCheckM ext cblocks blocks tops ret r ps r ps
           (TopPermCheckState ext cblocks blocks tops ret)
top_get = gcaptureCC $ \k -> ask >>= k

lookupBlockInfo :: Member blocks args ->
                   PermCheckM ext cblocks blocks tops ret r ps r ps
                   (BlockInfo ext blocks tops ret args)
lookupBlockInfo memb =
  top_get >>>= \top_st ->
  greturn (mapRListLookup memb $ stBlockInfo top_st)

getNextEntryID :: Member blocks args -> CruCtx ghosts ->
                  PermCheckM ext cblocks blocks tops ret r ps r ps
                  (TypedEntryID blocks args ghosts)
getNextEntryID memb ghosts =
  (stBlockInfo <$> top_get) >>>= \blkMap ->
  liftPermCheckM (innerBlockInfo <$> unClosed <$> get) >>>= \deltas ->
  let max_ix1 =
        foldr (max . entryInfoIndex) 0 $
        blockInfoEntries $ mapRListLookup memb blkMap in
  let max_ix =
        foldr (max . entryInfoIndex) max_ix1 $
        getDeltaEntriesForBlock memb deltas in
  greturn (TypedEntryID memb ghosts (max_ix + 1))

insNewBlockEntry :: Member blocks args -> CruCtx args -> CruCtx ghosts ->
                    Closed (MbValuePerms ((tops :++: args) :++: ghosts)) ->
                    PermCheckM ext cblocks blocks tops ret r ps r ps
                    (TypedEntryID blocks args ghosts)
insNewBlockEntry memb args ghosts perms_in =
  do entryID <- getNextEntryID memb ghosts
     topCtx <- stTopCtx <$> top_get
     liftPermCheckM $ modify $ \cl_st ->
       $(mkClosed [| \st delta ->
                    st { innerBlockInfo =
                           innerBlockInfo st ++ [delta] } |]) `clApply`
       cl_st `clApply`
       ($(mkClosed [| BlockInfoMapDelta |]) `clApply` toClosed memb `clApply`
        ($(mkClosed [| BlockEntryInfo |]) `clApply` toClosed entryID `clApply`
         toClosed topCtx `clApply` toClosed args `clApply` perms_in))
     return entryID

-- | Look up the current primary permission associated with a variable
getVarPerm :: ExprVar a ->
              PermCheckM ext cblocks blocks tops ret r ps r ps (ValuePerm a)
getVarPerm x = view (varPerm x) <$> stCurPerms <$> gget

-- | Set the current primary permission associated with a variable
setVarPerm :: ExprVar a -> ValuePerm a ->
              PermCheckM ext cblocks blocks tops ret r ps r ps ()
setVarPerm x p = gmodify $ modifySTCurPerms $ set (varPerm x) p

-- | Look up the current primary permission associated with a register
getRegPerm :: TypedReg a ->
              PermCheckM ext cblocks blocks tops ret r ps r ps (ValuePerm a)
getRegPerm (TypedReg x) = getVarPerm x

-- | Eliminate any disjunctions, existentials, or recursive permissions for a
-- register and then return the resulting "simple" permission, leaving it on the
-- top of the stack
getPushSimpleRegPerm :: TypedReg a ->
                        StmtPermCheckM ext cblocks blocks tops ret
                        (ps :> a) ps (ValuePerm a)
getPushSimpleRegPerm r =
  getRegPerm r >>>= \p_init ->
  embedImplM TypedImplStmt emptyCruCtx
  (implPushM (typedRegVar r) p_init >>>
   elimOrsExistsRecsM (typedRegVar r)) >>>= \(_, p_ret) ->
  greturn p_ret

-- | Eliminate any disjunctions, existentials, or recursive permissions for a
-- register and then return the resulting "simple" permission
getSimpleRegPerm :: TypedReg a ->
                    StmtPermCheckM ext cblocks blocks tops ret ps ps
                    (ValuePerm a)
getSimpleRegPerm r =
  snd <$> embedImplM TypedImplStmt emptyCruCtx (getSimpleVarPerm $
                                                typedRegVar r)

-- | A version of 'getEqualsExpr' for 'TypedReg's
getRegEqualsExpr ::
  TypedReg a ->
  StmtPermCheckM ext cblocks blocks tops ret ps ps (PermExpr a)
getRegEqualsExpr r =
  snd <$> embedImplM TypedImplStmt emptyCruCtx (getEqualsExpr $
                                                PExpr_Var $ typedRegVar r)

-- | Eliminate any disjunctions, existentials, recursive permissions, or
-- equality permissions for an LLVM register until we either get a conjunctive
-- permission for it or we get that it is equal to a bitvector word. In either
-- case, leave the resulting permission on the top of the stack and return its
-- contents as the return value.
getAtomicOrWordLLVMPerms ::
  (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
  StmtPermCheckM ext cblocks blocks tops ret
  (ps :> LLVMPointerType w)
  ps
  (Either (PermExpr (BVType w)) [AtomicPerm (LLVMPointerType w)])
getAtomicOrWordLLVMPerms r =
  let x = typedRegVar r in
  getPushSimpleRegPerm r >>>= \p ->
  case p of
    ValPerm_Conj ps ->
      greturn $ Right ps
    ValPerm_Eq (PExpr_Var y) ->
      embedImplM TypedImplStmt emptyCruCtx
      (introEqCopyM x (PExpr_Var y) >>> recombinePerm x p) >>>
      getAtomicOrWordLLVMPerms (TypedReg y) >>>= \eith ->
      case eith of
        Left e ->
          embedImplM TypedImplStmt emptyCruCtx
          (introCastM x y $ ValPerm_Eq $ PExpr_LLVMWord e) >>>
          greturn (Left e)
        Right ps ->
          embedImplM TypedImplStmt emptyCruCtx (introCastM x y $
                                                ValPerm_Conj ps) >>>
          greturn (Right ps)
    ValPerm_Eq e@(PExpr_LLVMOffset y off) ->
      embedImplM TypedImplStmt emptyCruCtx
      (introEqCopyM x e >>> recombinePerm x p) >>>
      getAtomicOrWordLLVMPerms (TypedReg y) >>>= \eith ->
      case eith of
        Left e ->
          embedImplM TypedImplStmt emptyCruCtx (offsetLLVMWordM y e off x) >>>
          greturn (Left $ bvAdd e off)
        Right ps ->
          embedImplM TypedImplStmt emptyCruCtx (castLLVMPtrM y ps off x) >>>
          greturn (Right $ mapMaybe (offsetLLVMAtomicPerm $ bvNegate off) ps)
    ValPerm_Eq e@(PExpr_LLVMWord e_word) ->
      embedImplM TypedImplStmt emptyCruCtx (introEqCopyM x e >>>
                                            recombinePerm x p) >>>
      greturn (Left e_word)


-- | Like 'getAtomicOrWordLLVMPerms', but fail if an equality permission to a
-- bitvector word is found
getAtomicLLVMPerms :: (1 <= w, KnownNat w) => TypedReg (LLVMPointerType w) ->
                      StmtPermCheckM ext cblocks blocks tops ret
                      (ps :> LLVMPointerType w)
                      ps
                      [AtomicPerm (LLVMPointerType w)]
getAtomicLLVMPerms r =
  getAtomicOrWordLLVMPerms r >>>= \eith ->
  case eith of
    Right ps -> greturn ps
    Left e ->
      stmtFailM (\i ->
                  sep [string "getAtomicLLVMPerms:",
                       string "Needed atomic permissions for" <+> permPretty i r,
                       string "but found" <+>
                       permPretty i (ValPerm_Eq $ PExpr_LLVMWord e)])


-- | Look up the function permission associated with a typed register
getRegFunPerm :: TypedReg (FunctionHandleType cargs fret) ->
                 StmtPermCheckM ext cblocks blocks tops ret ps ps
                 (SomeFunPerm (CtxToRList cargs) fret)
getRegFunPerm freg =
  (stPermEnv <$> top_get) >>>= \env ->
  getSimpleRegPerm freg >>>= \p_freg ->
  case p_freg of
    ValPerm_Eq (PExpr_Fun f)
      | Just (some_fun_perm, _) <- lookupFunPerm env f ->
          greturn some_fun_perm
    ValPerm_Conj [Perm_Fun fun_perm] -> greturn (SomeFunPerm fun_perm)
    _ -> stmtFailM (\i ->
                     string "No function permission for" <+> permPretty i freg)

-- | Pretty-print the permissions that are "relevant" to a register, which
-- includes its permissions and all those relevant to any register it is equal
-- to, possibly plus some offset
ppRelevantPerms :: TypedReg tp ->
                   PermCheckM ext cblocks blocks tops ret r ps r ps Doc
ppRelevantPerms r =
  getRegPerm r >>>= \p ->
  permGetPPInfo >>>= \ppInfo ->
  let pp_r = permPretty ppInfo r <> colon <> permPretty ppInfo p in
  case p of
    ValPerm_Eq (PExpr_Var x) ->
      ((pp_r <> comma) <+>) <$> ppRelevantPerms (TypedReg x)
    ValPerm_Eq (PExpr_LLVMOffset x _) ->
      ((pp_r <> comma) <+>) <$> ppRelevantPerms (TypedReg x)
    _ -> greturn pp_r

-- | Pretty-print a Crucible 'Reg' and what 'TypedReg' it is equal to, along
-- with the relevant permissions for that 'TypedReg'
ppCruRegAndPerms :: CtxTrans ctx -> Reg ctx a ->
                    PermCheckM ext cblocks blocks tops ret r ps r ps Doc
ppCruRegAndPerms ctx r =
  permGetPPInfo >>>= \ppInfo ->
  ppRelevantPerms (tcReg ctx r) >>>= \pp ->
  greturn (PP.group (pretty r <+> char '=' <+> permPretty ppInfo (tcReg ctx r)
                     <> comma <+> pp))

-- | Find all the variables of LLVM frame pointer type in a sequence
-- FIXME: move to Permissions.hs
findLLVMFrameVars :: NatRepr w -> CruCtx as -> MapRList Name as ->
                     [ExprVar (LLVMFrameType w)]
findLLVMFrameVars _ CruCtxNil _ = []
findLLVMFrameVars w (CruCtxCons tps (LLVMFrameRepr w')) (ns :>: n) =
  case testEquality w w' of
    Just Refl -> n : findLLVMFrameVars w tps ns
    Nothing -> error "findLLVMFrameVars: found LLVM frame pointer of wrong type"
findLLVMFrameVars w (CruCtxCons tps _) (ns :>: _) = findLLVMFrameVars w tps ns


-- | Get the current frame pointer on LLVM architectures
getFramePtr :: PermCheckM (LLVM arch) cblocks blocks tops ret r ps r ps
               (Maybe (TypedReg (LLVMFrameType (ArchWidth arch))))
getFramePtr = gget >>>= \st -> case stExtState st of
  PermCheckExtState_LLVM maybe_fp -> greturn maybe_fp

-- | Set the current frame pointer on LLVM architectures
setFramePtr :: TypedReg (LLVMFrameType (ArchWidth arch)) ->
               PermCheckM (LLVM arch) cblocks blocks tops ret r ps r ps ()
setFramePtr fp =
  gmodify (\st -> st { stExtState = PermCheckExtState_LLVM (Just fp) })

-- | Look up the type of a free variable, or raise an error if it is unknown
getVarType :: ExprVar a ->
              PermCheckM ext cblocks blocks tops ret r ps r ps (TypeRepr a)
getVarType x =
  (NameMap.lookup x <$> stVarTypes <$> gget) >>>= \maybe_tp ->
  case maybe_tp of
    Just tp -> greturn tp
    Nothing ->
      stmtTraceM (\i -> string "getVarType: could not find type for variable:"
                        <+> permPretty i x) >>>
      error "getVarType"

-- | Look up the types of multiple free variables
getVarTypes :: MapRList Name tps ->
               PermCheckM ext cblocks blocks tops ret r ps r ps (CruCtx tps)
getVarTypes MNil = greturn CruCtxNil
getVarTypes (xs :>: x) = CruCtxCons <$> getVarTypes xs <*> getVarType x

-- | Remember the type of a free variable, and ensure that it has a permission
setVarType :: ExprVar a -> TypeRepr a ->
              PermCheckM ext cblocks blocks tops ret r ps r ps ()
setVarType x tp =
  gmodify $ \st ->
  st { stCurPerms = initVarPerm x (stCurPerms st),
       stVarTypes = NameMap.insert x tp (stVarTypes st),
       stPPInfo = ppInfoAddExprName "x" x (stPPInfo st) }

-- | Remember the types of a sequence of free variables
setVarTypes :: MapRList Name tps -> CruCtx tps ->
               PermCheckM ext cblocks blocks tops ret r ps r ps ()
setVarTypes _ CruCtxNil = greturn ()
setVarTypes (xs :>: x) (CruCtxCons tps tp) =
  setVarTypes xs tps >>> setVarType x tp

-- | Get the current 'PPInfo'
permGetPPInfo :: PermCheckM ext cblocks blocks tops ret r ps r ps PPInfo
permGetPPInfo = stPPInfo <$> get

-- | Emit debugging output using the current 'PPInfo'
stmtTraceM :: (PPInfo -> Doc) ->
              PermCheckM ext cblocks blocks tops ret r ps r ps String
stmtTraceM f =
  (f <$> permGetPPInfo) >>>= \doc ->
  let str = renderDoc doc in
  trace str (greturn str)

-- | Failure in the statement permission-checking monad
stmtFailM :: (PPInfo -> Doc) -> PermCheckM ext cblocks blocks tops ret r1 ps1
             (TypedStmtSeq ext blocks tops ret ps2) ps2 a
stmtFailM msg =
  stmtTraceM (\i -> string "Type-checking failure:" <+> msg i) >>>= \str ->
  gabortM (return $ TypedImplStmt $
           PermImpl_Step (Impl1_Fail str) MbPermImpls_Nil)

-- | Smart constructor for applying a function on 'PermImpl's
applyImplFun :: (PermImpl r ps -> r ps) -> PermImpl r ps -> r ps
applyImplFun _ (PermImpl_Done r) = r
applyImplFun f impl = f impl

-- | FIXME HERE: Make 'ImplM' quantify over any underlying monad, so that we do
-- not have to use 'traversePermImpl' after we run an 'ImplM'
data WithImplState vars a ps ps' =
  WithImplState a (ImplState vars ps) (ps' :~: ps)

-- | Call 'runImplM' in the 'PermCheckM' monad
pcmRunImplM ::
  CruCtx vars -> (a -> r ps_out) ->
  ImplM vars (InnerPermCheckState blocks tops ret) r ps_out ps_in a ->
  PermCheckM ext cblocks blocks tops ret r' ps_in r' ps_in
  (PermImpl r ps_in)
pcmRunImplM vars retF impl_m =
  (stCurPerms <$> gget) >>>= \perms_in ->
  (stPermEnv <$> top_get) >>>= \env ->
  (stPPInfo <$> gget) >>>= \ppInfo ->
  (stVarTypes <$> gget) >>>= \varTypes ->
  liftPermCheckM $ lift $
  runImplM vars perms_in env ppInfo varTypes (return . retF . fst) impl_m

-- | Embed an implication computation inside a permission-checking computation
embedImplM ::
  (forall ps. PermImpl r ps -> r ps) -> CruCtx vars ->
  ImplM vars (InnerPermCheckState blocks tops ret) r ps_out ps_in a ->
  PermCheckM ext cblocks blocks tops ret (r ps_out) ps_out (r ps_in) ps_in
  (PermSubst vars, a)
embedImplM f_impl vars m =
  gmapRet (f_impl <$>) >>>
  (stCurPerms <$> gget) >>>= \perms_in ->
  (stPermEnv <$> top_get) >>>= \env ->
  (stPPInfo <$> gget) >>>= \ppInfo ->
  (stVarTypes <$> gget) >>>= \varTypes ->
  (gcaptureCC $ \k ->
    ask >>= \r ->
    lift $
    runImplM vars perms_in env ppInfo varTypes (flip runReaderT r
                                                . k) m) >>>= \(a, implSt) ->
  gmodify ((\st -> st { stPPInfo = implSt ^. implStatePPInfo,
                        stVarTypes = implSt ^. implStateNameTypes })
           . setSTCurPerms (implSt ^. implStatePerms)) >>>
  greturn (completePSubst vars (implSt ^. implStatePSubst), a)

-- | Special case of 'embedImplM' for a statement type-checking context where
-- @vars@ is empty
stmtEmbedImplM ::
  ImplM RNil (InnerPermCheckState
              blocks tops ret) (TypedStmtSeq ext blocks tops ret) ps_out ps_in a ->
  StmtPermCheckM ext cblocks blocks tops ret ps_out ps_in a
stmtEmbedImplM m =
  embedImplM TypedImplStmt emptyCruCtx m >>>= \(_,a) -> greturn a


-- | Recombine any outstanding distinguished permissions back into the main
-- permission set, in the context of type-checking statements
stmtRecombinePerms ::
  StmtPermCheckM ext cblocks blocks tops ret RNil ps_in ()
stmtRecombinePerms =
  gget >>>= \st ->
  let dist_perms = view distPerms (stCurPerms st) in
  embedImplM TypedImplStmt emptyCruCtx (recombinePerms dist_perms) >>>= \_ ->
  greturn ()

stmtProvePerms' :: PermCheckExtC ext =>
                   CruCtx vars -> ExDistPerms vars ps ->
                   StmtPermCheckM ext cblocks blocks tops ret
                   ps RNil (PermSubst vars)
stmtProvePerms' vars ps =
  embedImplM TypedImplStmt vars (proveVarsImpl ps) >>>= \(s,_) ->
  greturn s

-- | Prove permissions in the context of type-checking statements
stmtProvePerms :: (PermCheckExtC ext, KnownRepr CruCtx vars) =>
                  ExDistPerms vars ps ->
                  StmtPermCheckM ext cblocks blocks tops ret
                  ps RNil (PermSubst vars)
stmtProvePerms ps = stmtProvePerms' knownRepr ps

-- | Prove a single permission in the context of type-checking statements
stmtProvePerm :: (PermCheckExtC ext, KnownRepr CruCtx vars) =>
                 TypedReg a -> Mb vars (ValuePerm a) ->
                 StmtPermCheckM ext cblocks blocks tops ret
                 (ps :> a) ps (PermSubst vars)
stmtProvePerm (TypedReg x) mb_p =
  embedImplM TypedImplStmt knownRepr (proveVarImpl x mb_p) >>>= \(s,_) ->
  greturn s

-- | Try to prove that a register equals a constant integer using equality
-- permissions in the context
resolveConstant :: TypedReg tp ->
                   StmtPermCheckM ext cblocks blocks tops ret ps ps
                   (Maybe Integer)
resolveConstant = helper . PExpr_Var . typedRegVar where
  helper :: PermExpr a ->
            StmtPermCheckM ext cblocks blocks tops ret ps ps
            (Maybe Integer)
  helper (PExpr_Var x) =
    getVarPerm x >>>= \p ->
    case p of
      ValPerm_Eq e -> helper e
      _ -> greturn Nothing
  helper (PExpr_Nat i) = greturn (Just i)
  helper (PExpr_BV factors off) =
    foldM (\maybe_res (BVFactor i x) ->
            helper (PExpr_Var x) >>= \maybe_x_val ->
            case (maybe_res, maybe_x_val) of
              (Just res, Just x_val) -> return (Just (res + x_val * i))
              _ -> return Nothing)
    (Just off) factors
  helper (PExpr_LLVMWord e) = helper e
  helper (PExpr_LLVMOffset x e) =
    do maybe_x_val <- helper (PExpr_Var x)
       maybe_e_val <- helper e
       case (maybe_x_val, maybe_e_val) of
         (Just x_val, Just e_val) -> return (Just (x_val + e_val))
         _ -> return Nothing
  helper _ = return Nothing


-- FIXME HERE: documentation!
convertRegType :: ExtRepr ext -> ProgramLoc ->
                  TypedReg tp1 -> TypeRepr tp1 -> TypeRepr tp2 ->
                  StmtPermCheckM ext cblocks blocks tops ret RNil RNil
                  (TypedReg tp2)
convertRegType _ _ reg tp1 tp2
  | Just Refl <- testEquality tp1 tp2 = greturn reg
convertRegType _ loc reg (BVRepr w1) tp2@(BVRepr w2)
  | Left LeqProof <- decideLeq (knownNat :: NatRepr 1) w2
  , NatCaseGT LeqProof <- testNatCases w1 w2 =
    withKnownNat w2 $
    emitStmt knownRepr loc (TypedSetReg tp2 $
                            TypedExpr (BVTrunc w2 w1 $ RegNoVal reg)
                            Nothing) >>>= \(_ :>: x) ->
    stmtRecombinePerms >>>
    greturn (TypedReg x)
convertRegType _ loc reg (BVRepr w1) tp2@(BVRepr w2)
  | Left LeqProof <- decideLeq (knownNat :: NatRepr 1) w1
  , Left LeqProof <- decideLeq (knownNat :: NatRepr 1) w2
  , NatCaseLT LeqProof <- testNatCases w1 w2 =
    withKnownNat w2 $
    emitStmt knownRepr loc (TypedSetReg tp2 $
                            TypedExpr (BVSext w2 w1 $ RegNoVal reg)
                            Nothing) >>>= \(_ :>: x) ->
    stmtRecombinePerms >>>
    greturn (TypedReg x)
convertRegType ExtRepr_LLVM loc reg (LLVMPointerRepr w1) (BVRepr w2)
  | Just Refl <- testEquality w1 w2 =
    withKnownNat w1 $
    stmtProvePerm reg llvmExEqWord >>>= \subst ->
    let e = substLookup subst Member_Base in
    emitLLVMStmt knownRepr loc (DestructLLVMWord reg e) >>>= \x ->
    stmtRecombinePerms >>>
    greturn (TypedReg x)
convertRegType ext loc reg (LLVMPointerRepr w1) (BVRepr w2) =
  convertRegType ext loc reg (LLVMPointerRepr w1) (BVRepr w1) >>>= \reg' ->
  convertRegType ext loc reg' (BVRepr w1) (BVRepr w2)
convertRegType ExtRepr_LLVM loc reg (BVRepr w2) (LLVMPointerRepr w1)
  | Just Refl <- testEquality w1 w2 =
    withKnownNat w1 $
    emitLLVMStmt knownRepr loc (ConstructLLVMWord reg) >>>= \x ->
    stmtRecombinePerms >>> greturn (TypedReg x)
convertRegType ext loc reg (BVRepr w1) (LLVMPointerRepr w2) =
  convertRegType ext loc reg (BVRepr w1) (BVRepr w2) >>>= \reg' ->
  convertRegType ext loc reg' (BVRepr w2) (LLVMPointerRepr w2)
convertRegType ext loc reg (LLVMPointerRepr w1) (LLVMPointerRepr w2) =
  convertRegType ext loc reg (LLVMPointerRepr w1) (BVRepr w1) >>>= \reg1 ->
  convertRegType ext loc reg1 (BVRepr w1) (BVRepr w2) >>>= \reg2 ->
  convertRegType ext loc reg2 (BVRepr w2) (LLVMPointerRepr w2)
convertRegType _ _ x tp1 tp2 =
  stmtFailM (\i -> string "Could not cast" <+> permPretty i x
                   <+> string "from" <+> string (show tp1)
                   <+> string "to" <+> string (show tp2))

-- | Emit a statement in the current statement sequence, where the supplied
-- function says how that statement modifies the current permissions, given the
-- freshly-bound names for the return values. Return those freshly-bound names
-- for the return values.
emitStmt :: TypeCtx rets => CruCtx rets -> ProgramLoc ->
            TypedStmt ext rets ps_in ps_out ->
            StmtPermCheckM ext cblocks blocks tops ret ps_out ps_in
            (MapRList Name rets)
emitStmt tps loc stmt =
  gopenBinding
  ((TypedConsStmt loc stmt <$>) . strongMbM)
  (nuMulti typeCtxProxies $ \vars -> ()) >>>= \(ns, ()) ->
  setVarTypes ns tps >>>
  gmodify (modifySTCurPerms $ applyTypedStmt stmt ns) >>>
  greturn ns


-- | Call emitStmt with a 'TypedLLVMStmt'
emitLLVMStmt :: TypeRepr tp -> ProgramLoc ->
                TypedLLVMStmt (ArchWidth arch) tp ps_in ps_out ->
                StmtPermCheckM (LLVM arch) cblocks blocks tops ret
                ps_out ps_in (Name tp)
emitLLVMStmt tp loc stmt =
  emitStmt (singletonCruCtx tp) loc (TypedLLVMStmt stmt) >>>= \(_ :>: n) ->
  greturn n

-- | A program location for code which was generated by the type-checker
checkerProgramLoc :: ProgramLoc
checkerProgramLoc =
  mkProgramLoc (functionNameFromText "None")
  (OtherPos "(Generated by permission type-checker)")

-- | Create a new lifetime @l@
beginLifetime :: StmtPermCheckM ext cblocks blocks tops ret
                 RNil RNil (ExprVar LifetimeType)
beginLifetime =
  emitStmt knownRepr checkerProgramLoc BeginLifetime >>>= \(_ :>: n) ->
  stmtTraceM (\i -> string "Beginning lifetime" <+> permPretty i n) >>>
  stmtRecombinePerms >>>
  greturn n

-- | End a lifetime
endLifetime :: PermCheckExtC ext => ExprVar LifetimeType ->
               StmtPermCheckM ext cblocks blocks tops ret RNil RNil ()
endLifetime l =
  stmtTraceM (\i -> string "Ending lifetime" <+> permPretty i l) >>>
  getVarPerm l >>>= \l_perm ->
  case l_perm of
    ValPerm_Conj [Perm_LOwned ps_list]
      | Some ps <- permListToDistPerms ps_list ->
        stmtProvePerms (distPermsToExDistPerms $
                        minLtEndPerms (PExpr_Var l) ps) >>>= \_ ->
        stmtProvePerm (TypedReg l) (emptyMb l_perm) >>>= \_ ->
        embedImplM TypedImplStmt CruCtxNil (buildLifetimeEndPerms
                                            l) >>>= \(_, some_end_perms) ->
        case some_end_perms of
          Some end_perms ->
            stmtTraceM (\i -> string "Dropping permissions:" <+>
                              permPretty i (lifetimeEndPermsToDistPerms
                                            end_perms)) >>>
            embedImplM TypedImplStmt CruCtxNil
            (implPushLifetimeEndPerms end_perms) >>>= \_ ->
            emitStmt knownRepr checkerProgramLoc
            (EndLifetime l ps ps_list (lifetimeEndPermsToDistPerms
                                       end_perms)) >>>= \_ ->
            stmtRecombinePerms
    _ -> stmtFailM (\i ->
                     string "endLifetime: no lowned permission for"
                     <+> permPretty i l)


----------------------------------------------------------------------
-- * Permission Checking for Expressions and Statements
----------------------------------------------------------------------

-- | Get a dynamic representation of an architecture's width
archWidth :: KnownNat (ArchWidth arch) => f arch -> NatRepr (ArchWidth arch)
archWidth _ = knownNat

-- | Type-check a Crucible register by looking it up in the translated context
tcReg :: CtxTrans ctx -> Reg ctx tp -> TypedReg tp
tcReg ctx (Reg ix) = ctx ! ix

-- | Type-check a Crucible register and also look up its value, if known
tcRegWithVal :: CtxTrans ctx -> Reg ctx tp ->
                StmtPermCheckM ext cblocks blocks tops ret ps ps
                (RegWithVal tp)
tcRegWithVal ctx r_untyped =
  let r = tcReg ctx r_untyped in
  getRegEqualsExpr r >>>= \e ->
  case e of
    PExpr_Var x | x == typedRegVar r -> greturn $ RegNoVal r
    _ -> greturn $ RegWithVal r e

-- | Type-check a sequence of Crucible registers
tcRegs :: CtxTrans ctx -> Assignment (Reg ctx) tps -> TypedRegs (CtxToRList tps)
tcRegs ctx (viewAssign -> AssignEmpty) = TypedRegsNil
tcRegs ctx (viewAssign -> AssignExtend regs reg) =
  TypedRegsCons (tcRegs ctx regs) (tcReg ctx reg)


-- | Type-check a Crucibe block id into a 'Member' proof
tcBlockID :: BlockID cblocks args ->
             StmtPermCheckM ext cblocks blocks tops ret ps ps
             (Member blocks (CtxToRList args))
tcBlockID blkID = stLookupBlockID blkID <$> top_get

-- | Type-check a Crucible expression to test if it has a statically known
-- 'PermExpr' value that we can use as an @eq(e)@ permission on the output of
-- the expression
tcExpr :: PermCheckExtC ext => App ext RegWithVal tp ->
          StmtPermCheckM ext cblocks blocks tops ret ps ps
          (Maybe (PermExpr tp))
tcExpr (ExtensionApp e_ext :: App ext RegWithVal tp)
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = error "tcExpr: unexpected LLVM expression"

-- Equality expressions --

tcExpr (BaseIsEq _ rwv1 rwv2)
  | regWithValExpr rwv1 == regWithValExpr rwv2 =
    greturn $ Just $ PExpr_Bool True
tcExpr (BaseIsEq _ (RegWithVal _ (PExpr_Bool b1))
        (RegWithVal _ (PExpr_Bool b2))) =
  greturn $ Just $ PExpr_Bool (b1 == b2)
tcExpr (BaseIsEq _ (RegWithVal _ (PExpr_Nat i1))
        (RegWithVal _ (PExpr_Nat i2))) =
  greturn $ Just $ PExpr_Bool (i1 == i2)
tcExpr (BaseIsEq (BaseBVRepr _) (RegWithVal _ bv1) (RegWithVal _ bv2))
  | bvEq bv1 bv2 = greturn $ Just $ PExpr_Bool True
tcExpr (BaseIsEq (BaseBVRepr _) (RegWithVal _ bv1) (RegWithVal _ bv2))
  | not (bvCouldEqual bv1 bv2) = greturn $ Just $ PExpr_Bool False

-- Boolean expressions --

tcExpr (BoolLit b) = greturn $ Just $ PExpr_Bool b

tcExpr (Not (RegWithVal _ (PExpr_Bool b))) =
  greturn $ Just $ PExpr_Bool $ not b

tcExpr (And (RegWithVal _ (PExpr_Bool False)) _) =
  greturn $ Just $ PExpr_Bool False
tcExpr (And _ (RegWithVal _ (PExpr_Bool False))) =
  greturn $ Just $ PExpr_Bool False
tcExpr (And (RegWithVal _ (PExpr_Bool True)) rwv) =
  greturn $ Just $ regWithValExpr rwv
tcExpr (And rwv (RegWithVal _ (PExpr_Bool True))) =
  greturn $ Just $ regWithValExpr rwv

tcExpr (Or (RegWithVal _ (PExpr_Bool True)) _) =
  greturn $ Just $ PExpr_Bool True
tcExpr (Or _ (RegWithVal _ (PExpr_Bool True))) =
  greturn $ Just $ PExpr_Bool True
tcExpr (Or (RegWithVal _ (PExpr_Bool False)) rwv) =
  greturn $ Just $ regWithValExpr rwv
tcExpr (Or rwv (RegWithVal _ (PExpr_Bool False))) =
  greturn $ Just $ regWithValExpr rwv

tcExpr (BoolXor (RegWithVal _ (PExpr_Bool False)) rwv) =
  greturn $ Just $ regWithValExpr rwv
tcExpr (BoolXor rwv (RegWithVal _ (PExpr_Bool False))) =
  greturn $ Just $ regWithValExpr rwv
tcExpr (BoolXor (RegWithVal _ (PExpr_Bool True))
        (RegWithVal _ (PExpr_Bool True))) =
  greturn $ Just $ PExpr_Bool False

-- Nat expressions --

tcExpr (NatLit i) = greturn $ Just $ PExpr_Nat $ toInteger i

-- Bitvector expressions --

tcExpr (BVLit w i) = withKnownNat w $ greturn $ Just $ bvInt i

tcExpr (BVSext w2 _ (RegWithVal _ (bvMatchConst -> Just i))) =
  withKnownNat w2 $ greturn $ Just $ bvInt i

tcExpr (BVAdd w (RegWithVal _ e1) (RegWithVal _ e2)) =
  withKnownNat w $ greturn $ Just $ bvAdd e1 e2

tcExpr (BVMul w (RegWithVal _ (bvMatchConst -> Just i)) (RegWithVal _ e)) =
  withKnownNat w $ greturn $ Just $ bvMult i e
tcExpr (BVMul w (RegWithVal _ e) (RegWithVal _ (bvMatchConst -> Just i))) =
  withKnownNat w $ greturn $ Just $ bvMult i e

tcExpr (BoolToBV w (RegWithVal _ (PExpr_Bool True))) =
  withKnownNat w $ greturn $ Just $ bvInt 1
tcExpr (BoolToBV w (RegWithVal _ (PExpr_Bool False))) =
  withKnownNat w $ greturn $ Just $ bvInt 0

tcExpr (BVUlt w (RegWithVal _ e1) (RegWithVal _ e2))
  | bvLt e1 e2 = greturn $ Just $ PExpr_Bool True
tcExpr (BVUlt w (RegWithVal _ e1) (RegWithVal _ e2))
  | not (bvCouldBeLt e1 e2) = greturn $ Just $ PExpr_Bool False
tcExpr (BVUle w (RegWithVal _ e1) (RegWithVal _ e2))
  | bvLt e2 e1 = greturn $ Just $ PExpr_Bool False
tcExpr (BVUle w (RegWithVal _ e1) (RegWithVal _ e2))
  | not (bvCouldBeLt e2 e1) = greturn $ Just $ PExpr_Bool True

tcExpr (BVSlt w (RegWithVal _ e1) (RegWithVal _ e2))
  | bvSLt e1 e2 = greturn $ Just $ PExpr_Bool True
tcExpr (BVSlt w (RegWithVal _ e1) (RegWithVal _ e2))
  | not (bvCouldBeSLt e1 e2) = greturn $ Just $ PExpr_Bool False
tcExpr (BVSle w (RegWithVal _ e1) (RegWithVal _ e2))
  | bvSLt e2 e1 = greturn $ Just $ PExpr_Bool False
tcExpr (BVSle w (RegWithVal _ e1) (RegWithVal _ e2))
  | not (bvCouldBeSLt e2 e1) = greturn $ Just $ PExpr_Bool True

tcExpr (BVNonzero w (RegWithVal _ bv))
  | bvEq bv (withKnownNat w $ bvInt 0) = greturn $ Just $ PExpr_Bool False
tcExpr (BVNonzero w (RegWithVal _ bv))
  | not (bvZeroable bv) = greturn $ Just $ PExpr_Bool True

-- Misc expressions --

tcExpr (WithAssertion tp (PartialExp _ (regWithValExpr -> e))) =
  greturn $ Just e

tcExpr _ = greturn Nothing


-- | Get the Boolean value of an 'AssertionClassifierTree' if it has one
assertionTreeVal :: ExtRepr ext -> AssertionClassifierTree ext RegWithVal ->
                    Maybe Bool
assertionTreeVal ExtRepr_LLVM (AT.Leaf a)
  | RegWithVal _ (PExpr_Bool b) <- a ^. predicate = Just b
assertionTreeVal _ _ = Nothing

-- | Simplify an 'AssertionTree'
simplAssertionTree :: ExtRepr ext -> AssertionClassifierTree ext RegWithVal ->
                      AssertionClassifierTree ext RegWithVal
simplAssertionTree _ atree@(AT.Leaf _) = atree
simplAssertionTree ext (AT.And atrees) =
  let atrees_simp = NonEmpty.map (simplAssertionTree ext) atrees in
  case foldr (\atree restM -> case assertionTreeVal ext atree of
                 Just True -> restM
                 Just False -> Left atree
                 _ -> (atree :) <$> restM) (return []) atrees_simp of
    Left a -> a
    Right (a:as) -> AT.And (a NonEmpty.:| as)
    Right [] -> NonEmpty.head atrees_simp
simplAssertionTree ext (AT.Or atrees) =
  let atrees_simp = NonEmpty.map (simplAssertionTree ext) atrees in
  case foldr (\atree restM -> case assertionTreeVal ext atree of
                 Just False -> restM
                 Just True -> Left atree
                 _ -> (atree :) <$> restM) (return []) atrees_simp of
    Left a -> a
    Right (a:as) -> AT.Or (a NonEmpty.:| as)
    Right [] -> NonEmpty.head atrees_simp
simplAssertionTree ext (AT.Ite rwv atree1 _)
  | PExpr_Bool True <- regWithValExpr rwv =
    simplAssertionTree ext atree1
simplAssertionTree ext (AT.Ite rwv _ atree2)
  | PExpr_Bool False <- regWithValExpr rwv =
    simplAssertionTree ext atree2
simplAssertionTree ext (AT.Ite rwv atree1 atree2) =
  AT.Ite rwv (simplAssertionTree ext atree1) (simplAssertionTree ext atree2)


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitStmt :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
              Stmt ext ctx ctx' ->
              StmtPermCheckM ext cblocks blocks tops ret RNil RNil
              (CtxTrans ctx')
tcEmitStmt ctx loc stmt =
  stmtTraceM (const (string "Type-checking statement:" <+>
                     ppStmt (size ctx) stmt)) >>>
  permGetPPInfo >>>= \ppInfo ->
  mapM (\(Some r) -> ppCruRegAndPerms ctx r)
  (stmtInputRegs stmt) >>>= \pps ->
  stmtTraceM (const (string "Input perms:" </> ppCommaSep pps)) >>>
  tcEmitStmt' ctx loc stmt >>>= \ctx' ->
  mapM (\(Some r) -> ppCruRegAndPerms ctx' r) (stmtOutputRegs
                                               (Ctx.size ctx')
                                               stmt) >>>= \pps ->
  stmtTraceM (const (string "Output perms:" </> ppCommaSep pps)) >>>
  greturn ctx'


tcEmitStmt' :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
               Stmt ext ctx ctx' ->
               StmtPermCheckM ext cblocks blocks tops ret RNil RNil
               (CtxTrans ctx')

tcEmitStmt' ctx loc (SetReg tp (App (ExtensionApp e_ext
                                     :: App ext (Reg ctx) tp)))
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = tcEmitLLVMSetExpr Proxy ctx loc e_ext

tcEmitStmt' ctx loc (SetReg tp (App e@(WithAssertion _ _
                                       :: App ext (Reg ctx) tp))) =
  let ext :: ExtRepr ext = knownRepr in
  traverseFC (tcRegWithVal ctx) e >>>= \e_with_vals ->
  let (atree, rwv) = case e_with_vals of
        WithAssertion _ (PartialExp atree rwv) -> (atree, rwv) in
  let atree_simp = simplAssertionTree ext atree in
  case assertionTreeVal ext atree_simp of
    Just True ->
      emitStmt (singletonCruCtx tp) loc (TypedSetRegPermExpr tp $
                                         regWithValExpr rwv) >>>= \(_ :>: x) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx x)
    Just False ->
      stmtFailM (\_ -> string "Failed assertion")
    _ ->
      let typed_e =
            TypedExpr (WithAssertion tp (PartialExp atree_simp rwv))
            (Just (regWithValExpr rwv)) in
      emitStmt (singletonCruCtx tp) loc (TypedSetReg tp typed_e) >>>= \(_ :>: x) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx x)

tcEmitStmt' ctx loc (SetReg tp (App e)) =
  traverseFC (tcRegWithVal ctx) e >>>= \e_with_vals ->
  tcExpr e_with_vals >>>= \maybe_val ->
  let typed_e = TypedExpr e_with_vals maybe_val in
  emitStmt (singletonCruCtx tp) loc (TypedSetReg tp typed_e) >>>= \(_ :>: x) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx x)

tcEmitStmt' ctx loc (ExtendAssign stmt_ext :: Stmt ext ctx ctx')
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = tcEmitLLVMStmt Proxy ctx loc stmt_ext

tcEmitStmt' ctx loc (CallHandle ret freg_untyped args_ctx args_untyped) =
  let freg = tcReg ctx freg_untyped
      args = tcRegs ctx args_untyped in
  getRegFunPerm freg >>>= \some_fun_perm ->
  case some_fun_perm of
    SomeFunPerm fun_perm ->
      (stmtProvePerms' (funPermGhosts fun_perm)
       (funPermExDistIns fun_perm (typedRegsToVars args))) >>>= \ghosts ->
      stmtProvePerm freg (emptyMb $ ValPerm_Conj1 $ Perm_Fun fun_perm) >>>= \_ ->
      (emitStmt (singletonCruCtx ret) loc
       (TypedCall freg fun_perm (exprsOfSubst ghosts) args)) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

tcEmitStmt' ctx loc (Assert reg msg) =
  let treg = tcReg ctx reg in
  getRegEqualsExpr treg >>>= \treg_expr ->
  case treg_expr of
    PExpr_Bool True -> greturn ctx
    PExpr_Bool False -> stmtFailM (\_ -> string "Failed assertion")
    _ ->
      emitStmt CruCtxNil loc (TypedAssert (tcReg ctx reg) (tcReg ctx msg)) >>>= \_ ->
      greturn ctx

tcEmitStmt' _ _ _ = error "tcEmitStmt: unsupported statement"


-- | Translate a Crucible assignment of an LLVM expression
tcEmitLLVMSetExpr ::
  (1 <= ArchWidth arch, KnownNat (ArchWidth arch)) => Proxy arch ->
  CtxTrans ctx -> ProgramLoc -> LLVMExtensionExpr arch (Reg ctx) tp ->
  StmtPermCheckM (LLVM arch) cblocks blocks tops ret RNil RNil
  (CtxTrans (ctx ::> tp))

-- Type-check a pointer-building expression, which is only valid when the block
-- = 0, i.e., when building a word
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerExpr w blk_reg off_reg) =
  let toff_reg = tcReg ctx off_reg
      tblk_reg = tcReg ctx blk_reg in
  resolveConstant tblk_reg >>>= \maybe_const ->
  case maybe_const of
    Just 0 ->
      withKnownNat w $
      emitLLVMStmt knownRepr loc (ConstructLLVMWord toff_reg) >>>= \x ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx x)
    _ -> stmtFailM (\i -> "LLVM_PointerExpr: Non-zero pointer block: "
                          <> permPretty i tblk_reg)

-- Type-check the LLVM value destructor that gets the block value, by either
-- proving a permission eq(llvmword e) and returning block 0 or proving
-- permission is_llvmptr and returning the constant value 1.
--
-- NOTE: our SAW translation does not include any computational content for
-- pointer blocks and offsets, so we cannot represent the actual runtime value
-- of the pointer block of a pointer. We can only know if it is zero or not by
-- using permissions, and we map all non-zero values to 1. This implicitly
-- assumes that the behavior of the program we are verifying is not altered in a
-- meaningful way by mapping the return value of 'LLVM_PointerBlock' to 1 when
-- it is applied to pointers, which is the case for all programs currently
-- generated by Crucible from LLVM.
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerBlock w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg
      x = typedRegVar tptr_reg in
  withKnownNat w $
  getAtomicOrWordLLVMPerms tptr_reg >>>= \eith ->
  case eith of
    Left e ->
      emitLLVMStmt knownRepr loc (AssertLLVMWord tptr_reg e) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Right ps ->
      stmtRecombinePerms >>>
      stmtProvePerm tptr_reg (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr tptr_reg) >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (NatLit 1)
                              (Just $ PExpr_Nat 1)) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

-- Type-check the LLVM value destructor that gets the offset value, by either
-- proving a permission eq(llvmword e) and returning e or proving
-- permission is_llvmptr and returning the constant bitvector value 0.
--
-- NOTE: Just as with 'LLVM_PointerBlock', because our SAW translation does not
-- include any computational content for pointer blocks and offsets, we cannot
-- represent the actual runtime value of the offset of a pointer. We thus return
-- 0 as a dummy value. This implicitly assumes that the behavior of the program
-- we are verifying is not altered in a meaningful way by mapping the return
-- value of 'LLVM_PointerOffset' to 0 when it is applied to pointers, which is
-- the case for all programs currently generated by Crucible from LLVM.
tcEmitLLVMSetExpr arch ctx loc (LLVM_PointerOffset w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg
      x = typedRegVar tptr_reg in
  withKnownNat w $
  getAtomicOrWordLLVMPerms tptr_reg >>>= \eith ->
  case eith of
    Left e ->
      emitLLVMStmt knownRepr loc (DestructLLVMWord
                                  tptr_reg e) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Right ps ->
      stmtRecombinePerms >>>
      stmtProvePerm tptr_reg (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr tptr_reg) >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (BVLit w 0)
                              (Just $ bvInt 0)) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)


-- FIXME HERE: move withLifetimeCurrentPerms somewhere better...

-- | Perform a statement type-checking conversation inside a context where the
-- supplied lifetime has been proved to be current using the supplied
-- 'LifetimeCurrentPerms'
withLifetimeCurrentPerms ::
  PermExpr LifetimeType ->
  (forall ps_l. LifetimeCurrentPerms ps_l ->
   StmtPermCheckM ext cblocks blocks tops ret (ps_out :++: ps_l)
   (ps_in :++: ps_l) a) ->
  StmtPermCheckM ext cblocks blocks tops ret ps_out ps_in a
withLifetimeCurrentPerms l m =
  -- Get the proof steps needed to prove that the lifetime l is current
  stmtEmbedImplM (getLifetimeCurrentPerms l) >>>= \some_cur_perms ->
  case some_cur_perms of
    Some cur_perms ->
      -- Prove that the required permissions
      stmtEmbedImplM (proveLifetimeCurrent cur_perms) >>>
      -- Perform the computation
      m cur_perms >>>= \a ->
      -- Recombine the proof that the lifetime is current
      stmtEmbedImplM (recombineLifetimeCurrentPerms cur_perms) >>>
      -- Finally, return the result
      greturn a


-- | Emit a 'TypedLLVMLoad' instruction, assuming the given LLVM field
-- permission is on the top of the stack. Prove the required lifetime
-- permissions as part of this process, and pop the resulting lifetime
-- permission off the stack before returning. Return the resulting return
-- register.
emitTypedLLVMLoad ::
  (1 <= w, KnownNat w, w ~ ArchWidth arch) =>
  Proxy arch -> ProgramLoc ->
  TypedReg (LLVMPointerType w) -> LLVMFieldPerm w -> DistPerms ps ->
  StmtPermCheckM (LLVM arch) cblocks blocks tops ret
  (ps :> LLVMPointerType w :> LLVMPointerType w)
  (ps :> LLVMPointerType w)
  (Name (LLVMPointerType (ArchWidth arch)))
emitTypedLLVMLoad _ loc treg fp ps =
  withLifetimeCurrentPerms (llvmFieldLifetime fp) $ \cur_perms ->
  emitLLVMStmt knownRepr loc (TypedLLVMLoad treg fp ps cur_perms)


-- | Emit a 'TypedLLVMStore' instruction, assuming the given LLVM field
-- permission is on the top of the stack. Prove the required lifetime
-- permissions as part of this process, and pop the resulting lifetime
-- permission off the stack before returning. Return the resulting return
-- register of unit type.
emitTypedLLVMStore ::
  (1 <= w, KnownNat w, w ~ ArchWidth arch) =>
  Proxy arch -> ProgramLoc ->
  TypedReg (LLVMPointerType (ArchWidth arch)) ->
  LLVMFieldPerm (ArchWidth arch) ->
  PermExpr (LLVMPointerType (ArchWidth arch)) -> DistPerms ps ->
  StmtPermCheckM (LLVM arch) cblocks blocks tops ret
  (ps :> LLVMPointerType w)
  (ps :> LLVMPointerType w)
  (Name UnitType)
emitTypedLLVMStore _ loc treg_ptr fp e ps =
  withLifetimeCurrentPerms (llvmFieldLifetime fp) $ \cur_perms ->
  emitLLVMStmt knownRepr loc (TypedLLVMStore treg_ptr fp e ps cur_perms)


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitLLVMStmt ::
  (1 <= w, KnownNat w, w ~ ArchWidth arch) => Proxy arch ->
  CtxTrans ctx -> ProgramLoc -> LLVMStmt w (Reg ctx) tp ->
  StmtPermCheckM (LLVM arch) cblocks blocks tops ret RNil RNil
  (CtxTrans (ctx ::> tp))

-- Type-check a load of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Load _ ptr tp _ _) =
  let tptr = tcReg ctx ptr in
  -- Prove [l]ptr ((0,rw) |-> eq(y)) for some l, rw, and y
  stmtProvePerm tptr llvmPtr0EqExPerm >>>= \impl_res ->
  let fp = subst impl_res llvmPtr0EqEx in
  -- Emit a TypedLLVMLoad instruction
  emitTypedLLVMLoad arch loc tptr fp DistPermsNil >>>= \z ->
  -- Recombine the resulting permissions onto the stack
  stmtRecombinePerms >>>
  -- Finally, convert the return value to the requested type and return it
  convertRegType knownRepr loc (TypedReg z) knownRepr tp >>>= \ret ->
  greturn (addCtxName ctx $ typedRegVar ret)


-- Type-check a store of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Store _ (ptr :: Reg ctx (LLVMPointerType w)) tp _ _ val) =
  let tptr :: TypedReg (LLVMPointerType w) = tcReg ctx ptr
      tval = tcReg ctx val
      tp_ptr = LLVMPointerRepr (knownRepr :: NatRepr w) in
  convertRegType knownRepr loc tval tp tp_ptr >>>= \tval_ptr ->
  stmtProvePerm tptr (llvmWriteTrueExLPerm $ bvInt 0) >>>= \subst ->
  let l = substLookup subst Member_Base in
  let fp = llvmFieldWriteTrueL (bvInt 0) l in
  emitTypedLLVMStore arch loc tptr fp
  (PExpr_Var $ typedRegVar tval_ptr) DistPermsNil >>>= \z ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx z)


{- FIXME HERE: old approach that performed the case split on the current perms
  getAtomicLLVMPerms tptr >>>= \ps ->
  stmtEmbedImplM
  (foldMapWithDefault implCatchM
   (implFailMsgM "LLVM_Store: could not find permission for offset 0")
   greturn
   (findMaybeIndices (llvmPermContainsOffset $ bvInt 0) ps)) >>>= \(i,_) ->
  case ps !! i of
    Perm_LLVMField fp
      | PExpr_Write <- llvmFieldRW fp ->
        -- If we found a field perm for offset 0, first extract it out of all
        -- the other perms for x and pop all the other perms off of the stack
        stmtEmbedImplM (implExtractConjM x ps i >>>
                        recombinePerm x (ValPerm_Conj (deleteNth i ps))) >>>
        -- Next, emit the typed LLVM store instruction
        emitTypedLLVMStore arch loc tptr fp tval_ptr DistPermsNil >>>= \z ->
        -- Finally, return the expanded context
        stmtRecombinePerms >>>
        greturn (addCtxName ctx z)

    Perm_LLVMArray ap
      | Just ix <- matchLLVMArrayField ap (bvInt 0) ->
        -- Extract the array perm we want out of the other perms on the stack
        -- and pop all the other perms off of the stack, then borrow the field
        -- corresopnding to offset 0
        stmtEmbedImplM (implExtractConjM x ps i >>>
                        recombinePerm x (ValPerm_Conj (deleteNth i ps)) >>>
                        implLLVMArrayIndexBorrow x ap ix) >>>= \(ap',fp) ->
        -- Emit the typed LLVM store instruction, noting that the array
        -- permission is on the stack below the borrowed field permission
        emitTypedLLVMStore arch loc tptr fp tval_ptr
        (distPerms1 x $ ValPerm_Conj1 $ Perm_LLVMArray ap') >>>= \z ->
        -- If the permissions in the array field are copyable, then copy them
        -- from the register value being stored and return the borrow; otherwise
        -- leave the borrow intact
        let field_p = llvmFieldContents fp in
        (if permIsCopyable field_p then
           stmtEmbedImplM
           (proveVarImpl (typedRegVar tval_ptr) (emptyMb field_p) >>>
            introLLVMFieldContentsM x (typedRegVar tval_ptr) >>>
            implLLVMArrayIndexReturn x ap' ix) >>>
           stmtRecombinePerms
         else
           stmtRecombinePerms) >>>
        -- Finally, return the expanded context
        greturn (addCtxName ctx z)

    _ ->
      error ("tcEmitLLVMStmt: LLVM_Store: "
             ++ "unexpected permission matched by llvmPermContainsOffset")
-}


-- Type-check an empty mem-clear instruction as a no-op
tcEmitLLVMStmt _ ctx loc (LLVM_MemClear _ _ 0) =
  emitStmt knownRepr loc (TypedSetReg knownRepr $
                          TypedExpr EmptyApp
                          (Just PExpr_Unit)) >>>= \(_ :>: z) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx z)

-- It is currently an error to clear a number of bytes that is not a multiple of
-- the machine word size, so throw an error
tcEmitLLVMStmt arch ctx loc (LLVM_MemClear _ ptr bytes)
  | bytesToBits bytes `mod` natValue (archWidth arch) /= 0 =
    stmtFailM (\_ -> string "LLVM_MemClear: size not a multiple of arch width")

-- Type-check a non-empty mem-clear instruction by writing a 0 to the last word
-- and then recursively clearing all but the last word
tcEmitLLVMStmt arch ctx loc (LLVM_MemClear mem ptr bytes) =
  let tptr = tcReg ctx ptr
      bytes' = bytes - bitsToBytes (intValue (archWidth arch))
      off = bytesToInteger bytes' in
  stmtProvePerm tptr (llvmWriteTrueExLPerm $ bvInt off) >>>= \subst ->
  let l = substLookup subst Member_Base in
  let fp = llvmFieldWriteTrueL (bvInt off) l in
  emitTypedLLVMStore arch loc tptr fp (PExpr_LLVMWord $
                                       bvInt 0) DistPermsNil >>>
  stmtRecombinePerms >>>
  tcEmitLLVMStmt arch ctx loc (LLVM_MemClear mem ptr bytes')

-- Type-check an alloca instruction
tcEmitLLVMStmt arch ctx loc (LLVM_Alloca w _ sz_reg _ _) =
  let sz_treg = tcReg ctx sz_reg in
  getFramePtr >>>= \maybe_fp ->
  maybe (greturn ValPerm_True) getRegPerm maybe_fp >>>= \fp_perm ->
  resolveConstant sz_treg >>>= \maybe_sz ->
  case (maybe_fp, fp_perm, maybe_sz) of
    (Just fp, ValPerm_Conj [Perm_LLVMFrame fperms], Just sz) ->
      stmtProvePerm fp (emptyMb fp_perm) >>>= \_ ->
      emitLLVMStmt knownRepr loc (TypedLLVMAlloca fp fperms sz) >>>= \y ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx y)
    (_, _, Nothing) ->
      stmtFailM (\i -> string "LLVM_Alloca: non-constant size for"
                       <+> permPretty i sz_treg)
    (Just fp, p, _) ->
      stmtFailM (\i -> string "LLVM_Alloca: expected LLVM frame perm for "
                       <+> permPretty i fp <> ", found perm"
                       <+> permPretty i p)
    (Nothing, _, _) ->
      stmtFailM (const $ string "LLVM_Alloca: no frame pointer set")

-- Type-check a push frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PushFrame _) =
  emitLLVMStmt knownRepr loc TypedLLVMCreateFrame >>>= \fp ->
  setFramePtr (TypedReg fp) >>>
  stmtRecombinePerms >>>
  emitStmt knownRepr loc (TypedSetReg knownRepr
                          (TypedExpr EmptyApp Nothing)) >>>= \(_ :>: y) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx y)

-- Type-check a pop frame instruction
tcEmitLLVMStmt arch ctx loc (LLVM_PopFrame _) =
  getFramePtr >>>= \maybe_fp ->
  maybe (greturn ValPerm_True) getRegPerm maybe_fp >>>= \fp_perm ->
  case (maybe_fp, fp_perm) of
    (Just fp, ValPerm_Conj [Perm_LLVMFrame fperms])
      | Some del_perms <- llvmFrameDeletionPerms fperms ->
        stmtProvePerms (distPermsToExDistPerms del_perms) >>>= \_ ->
        stmtProvePerm fp (emptyMb fp_perm) >>>= \_ ->
        emitLLVMStmt knownRepr loc (TypedLLVMDeleteFrame
                                    fp fperms del_perms) >>>= \y ->
        gmodify (\st -> st { stExtState = PermCheckExtState_LLVM Nothing }) >>>
        greturn (addCtxName ctx y)
    _ -> stmtFailM (const $ string "LLVM_PopFrame: no frame perms")

-- Type-check a pointer offset instruction by emitting OffsetLLVMValue
tcEmitLLVMStmt arch ctx loc (LLVM_PtrAddOffset w _ ptr off) =
  let tptr = tcReg ctx ptr
      toff = tcReg ctx off in
  getRegEqualsExpr toff >>>= \off_expr ->
  emitLLVMStmt knownRepr loc (OffsetLLVMValue tptr off_expr) >>>= \ret ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx ret)

-- Type-check a LoadHandle instruction by looking for a function pointer perm
tcEmitLLVMStmt arch ctx loc (LLVM_LoadHandle _ ptr args ret) =
  let tptr = tcReg ctx ptr
      x = typedRegVar tptr in
  getAtomicLLVMPerms tptr >>>= \ps ->
  case findIndex (\p -> case p of
                     Perm_LLVMFunPtr _ -> True
                     _ -> False) ps of
    Just i
      | Perm_LLVMFunPtr fun_perm <- ps!!i
      , Just Refl <- testEquality (funPermArgs fun_perm) (mkCruCtx args)
      , Just Refl <- testEquality (funPermRet fun_perm) ret ->
        stmtEmbedImplM (implCopyConjM x ps i >>>
                        recombinePerm x (ValPerm_Conj ps)) >>>
        emitLLVMStmt (FunctionHandleRepr args ret) loc
        (TypedLLVMLoadHandle tptr fun_perm) >>>= \ret ->
        stmtRecombinePerms >>>
        greturn (addCtxName ctx ret)

-- Type-check a LoadHandle instruction by looking for a function pointer perm
tcEmitLLVMStmt arch ctx loc (LLVM_ResolveGlobal w _ gsym) =
  (stPermEnv <$> top_get) >>>= \env ->
  case lookupGlobalSymbol env gsym w of
    Just (p, _) ->
      emitLLVMStmt knownRepr loc (TypedLLVMResolveGlobal gsym p) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Nothing ->
      stmtFailM (const $ string ("LLVM_ResolveGlobal: no perms for global "
                                 ++ show gsym))

tcEmitLLVMStmt arch ctx loc (LLVM_PtrEq _ r1 r2) =
  let x1 = tcReg ctx r1
      x2 = tcReg ctx r2 in
  getRegEqualsExpr x1 >>>= \e1 ->
  getRegEqualsExpr x2 >>>= \e2 ->
  case (e1, e2) of

    -- If both variables equal words, then compare the words
    --
    -- FIXME: if we have bvEq e1' e2' or not (bvCouldEqual e1' e2') then we
    -- should return a known Boolean value in place of the Nothing
    (PExpr_LLVMWord e1', PExpr_LLVMWord e2') ->
      emitStmt knownRepr loc (TypedSetRegPermExpr
                              knownRepr e1') >>>= \(_ :>: n1) ->
      stmtRecombinePerms >>>
      emitStmt knownRepr loc (TypedSetRegPermExpr
                              knownRepr e2') >>>= \(_ :>: n2) ->
      stmtRecombinePerms >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (BaseIsEq knownRepr
                                         (RegWithVal (TypedReg n1) e1')
                                         (RegWithVal (TypedReg n2) e2'))
                              Nothing) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

    -- If both variables equal x+off for the same x, compare the offsets
    --
    -- FIXME: test off1 == off2 like above
    (asLLVMOffset -> Just (x1', off1), asLLVMOffset -> Just (x2', off2))
      | x1' == x2' ->
        emitStmt knownRepr loc (TypedSetRegPermExpr
                                knownRepr off1) >>>= \(_ :>: n1) ->
        stmtRecombinePerms >>>
        emitStmt knownRepr loc (TypedSetRegPermExpr
                                knownRepr off2) >>>= \(_ :>: n2) ->
        stmtRecombinePerms >>>
        emitStmt knownRepr loc (TypedSetReg knownRepr $
                                TypedExpr (BaseIsEq knownRepr
                                           (RegWithVal (TypedReg n1) off1)
                                           (RegWithVal (TypedReg n2) off2))
                                Nothing) >>>= \(_ :>: ret) ->
        stmtRecombinePerms >>>
        greturn (addCtxName ctx ret)

    -- If one variable is a word and the other is not known to be a word, then
    -- that other has to be a pointer, in which case the comparison will
    -- definitely fail. Otherwise we cannot compare them and we fail.
    (PExpr_LLVMWord e, asLLVMOffset -> Just (x', _)) ->
      let r' = TypedReg x' in
      stmtProvePerm r' (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr r') >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (BoolLit False)
                              Nothing) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

    -- Symmetrical version of the above case
    (asLLVMOffset -> Just (x', _), PExpr_LLVMWord e) ->
      let r' = TypedReg x' in
      stmtProvePerm r' (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr r') >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (BoolLit False)
                              Nothing) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

    -- If we don't know any relationship between the two registers, then we
    -- fail, because there is no way to compare pointers in the translation
    _ ->
      stmtFailM (\i ->
                  sep [string "Could not compare LLVM pointer values",
                       permPretty i x1, string "and", permPretty i x2])


tcEmitLLVMStmt _arch _ctx _loc _stmt =
  error "tcEmitLLVMStmt: unimplemented statement"

-- FIXME HERE: need to handle PtrEq, PtrLe, and PtrSubtract


----------------------------------------------------------------------
-- * Permission Checking for Jump Targets and Termination Statements
----------------------------------------------------------------------

-- FIXME: no longer needed?
{-
mkEqVarPerms :: MapRList Name ctx -> MapRList Name ctx -> DistPerms ctx
mkEqVarPerms MNil _ = DistPermsNil
mkEqVarPerms (xs :>: x) (ys :>: y) =
  DistPermsCons (mkEqVarPerms xs ys) x (ValPerm_Eq $ PExpr_Var y)

-- | Take a set of permissions on some ghost variables as well as a set of
-- assignments @arg1=ghost1, ...@ of those ghost variables to the "real"
-- arguments of a block and add the permissions @arg1:eq(ghost1), ...@ to the
-- input permissions
buildInputPermsH :: Mb ghosts (DistPerms ghosts) ->
                    Mb ghosts (MapRList Name args) ->
                    MbDistPerms (ghosts :++: args)
buildInputPermsH mb_perms mb_args =
  mbCombine $ mbMap2 (\perms args ->
                        nuMulti args $ \arg_vars ->
                        appendDistPerms perms (mkEqVarPerms arg_vars args))
  mb_perms mb_args

buildInputPerms :: PPInfo -> MapRList Name (ghosts :: RList CrucibleType) ->
                   DistPerms ghosts -> MapRList Name args ->
                   Closed (MbDistPerms (ghosts :++: args))
buildInputPerms ppInfo xs perms_in args_in =
  $(mkClosed [| buildInputPermsH |])
  `clApply` maybe (error ("buildInputPerms:\n" ++
                          permPrettyString ppInfo xs ++ "\n" ++
                          permPrettyString ppInfo perms_in)) id
  (abstractVars xs perms_in)
  `clApply` maybe (error ("buildInputPerms: " ++
                          permPrettyString ppInfo args_in)) id
  (abstractVars xs args_in)

abstractPermsRet :: MapRList Name (ghosts :: RList CrucibleType) ->
                    MapRList f args ->
                    Binding (ret :: CrucibleType) (DistPerms ret_ps) ->
                    Closed (Mb (ghosts :++: args :> ret) (DistPerms ret_ps))
abstractPermsRet xs args ret_perms =
  $(mkClosed [| \args ->  mbCombine . mbCombine . fmap (nuMulti args . const) |])
  `clApply` closedProxies args
  `clApply` maybe (error "abstractPermsRet") id (abstractVars xs ret_perms)
-}

-- | Type-check a Crucible jump target
tcJumpTarget :: CtxTrans ctx -> JumpTarget cblocks ctx ->
                StmtPermCheckM ext cblocks blocks tops ret RNil RNil
                (PermImpl (TypedJumpTarget blocks tops) RNil)
tcJumpTarget ctx (JumpTarget blkID args_tps args) =
  top_get >>>= \top_st ->
  gget >>>= \st ->
  let tops_ns = stTopVars st
      args_t = tcRegs ctx args
      args_ns = typedRegsToVars args_t
      tops_args_ns = appendMapRList tops_ns args_ns in
  tcBlockID blkID >>>= \memb ->
  lookupBlockInfo memb >>>= \blkInfo ->

  -- First test if we have already visited the given block
  -- FIXME: don't add a new entrypoint if we have a block entry hint
  if blockInfoVisited blkInfo then
    -- If so, then jump to the first entry point, assuming there is one
    case blockInfoEntries blkInfo of
      [] -> error "tcJumpTarget: visited block has no entrypoints!"
      (BlockEntryInfo entryID _ _ entry_perms_in):_ ->

        -- Substitute the top-level and normal args into the input perms
        let ghosts = entryGhosts entryID
            ghosts_prxs = cruCtxProxies ghosts
            ex_perms =
              varSubst (permVarSubstOfNames tops_args_ns) $
              mbSeparate ghosts_prxs $
              mbValuePermsToDistPerms entry_perms_in in
        stmtTraceM (\i ->
                     string ("tcJumpTarget " ++ show blkID ++ " (visited)") </>
                     string "Input perms: " <+>
                     hang 2 (permPretty i ex_perms)) >>>

        -- Prove the required input perms for this entrypoint and return the
        -- jump target inside an implication
        pcmRunImplM ghosts
        (\ghosts_subst ->
          TypedJumpTarget entryID Proxy (mkCruCtx args_tps) $
          varSubst ghosts_subst ex_perms)
        (proveExVarsImpl ex_perms >>> getDistPerms >>>= \proved_perms ->
          greturn (permVarSubstOfNames $ distPermsVars $ snd $
                   splitDistPerms tops_args_ns ghosts_prxs proved_perms))

  else
    -- If not, we can make a new entrypoint that takes all of the current
    -- permissions as input
    --
    -- Step 1: compute the ghosts arguments as all variables needed in the
    -- permissions for the top-level and normal arguments
    (permCheckExtStateNames <$> stExtState <$> gget) >>>= \(Some ext_ns) ->
    let tops_set =
          foldrMapRList (\n ->
                          NameMap.insert n (Constant ()))
          NameMap.empty tops_ns
        cur_perms = stCurPerms st in
    case varPermsNeededVars (appendMapRList tops_args_ns ext_ns) cur_perms of
      Some ghosts_ns' ->
        -- Step 2: compute the permissions for the three sorts of arguments,
        -- where each normal argument that is also in the top-level arguments
        -- gets eq permissions
        let ghosts_ns = appendMapRList ext_ns ghosts_ns'
            cur_perms = stCurPerms st
            tops_perms = varPermsMulti tops_ns cur_perms
            ghosts_perms = varPermsMulti ghosts_ns cur_perms
            args_perms =
              buildDistPerms (\n -> if NameMap.member n tops_set then
                                      ValPerm_Eq (PExpr_Var n)
                                    else cur_perms ^. varPerm n) args_ns
            perms_in = appendDistPerms (appendDistPerms
                                        tops_perms args_perms) ghosts_perms in
        stmtTraceM (\i ->
                     string ("tcJumpTarget " ++ show blkID ++ " (unvisited)") </>
                     string "Input perms: " <+>
                     hang 2 (permPretty i perms_in)) >>>

        -- Step 3: abstract all the variables out of the input permissions. Note
        -- that abstractVars uses the left-most occurrence of any variable that
        -- occurs multiple times in the variable list and we want our eq perms
        -- for our args to map to our tops, not our args, so this order works
        -- for what we want
        let cl_mb_perms_in =
              case abstractVars
                   (appendMapRList (appendMapRList tops_ns args_ns) ghosts_ns)
                   (distPermsToValuePerms perms_in) of
                Just ps -> ps
                Nothing ->
                  error "tcJumpTarget: unexpected free variable in perms_in" in

        -- Step 4: insert a new block entrypoint that has all the permissions we
        -- constructed above as input permissions
        getVarTypes ghosts_ns >>>= \ghosts_tps ->
        (insNewBlockEntry
         memb (mkCruCtx args_tps) ghosts_tps cl_mb_perms_in) >>>= \entryID ->

        -- Step 5: return a TypedJumpTarget inside a PermImpl that proves all
        -- the required input permissions from the current permission set. This
        -- proof just copies the existing permissions into the current
        -- distinguished perms, except for the eq permissions for real
        -- arguments, which are proved by reflexivity.
        let target_t =
              TypedJumpTarget entryID Proxy (mkCruCtx args_tps) perms_in in
        pcmRunImplM CruCtxNil (const target_t) (implPushOrReflMultiM perms_in)


-- | Type-check a termination statement
tcTermStmt :: PermCheckExtC ext => CtxTrans ctx ->
              TermStmt cblocks ret ctx ->
              StmtPermCheckM ext cblocks blocks tops ret RNil RNil
              (TypedTermStmt blocks tops ret RNil)
tcTermStmt ctx (Jump tgt) =
  TypedJump <$> tcJumpTarget ctx tgt
tcTermStmt ctx (Br reg tgt1 tgt2) =
  -- FIXME: Instead of mapping Br to TypedJump when the jump target is known,
  -- make a version of TypedBr that still stores the JumpTargets of never-taken
  -- branches in order to allow translating back to untyped Crucible
  let treg = tcReg ctx reg in
  getRegEqualsExpr treg >>>= \treg_expr ->
  case treg_expr of
    PExpr_Bool True -> TypedJump <$> tcJumpTarget ctx tgt1
    PExpr_Bool False -> TypedJump <$> tcJumpTarget ctx tgt2
    _ -> TypedBr treg <$> tcJumpTarget ctx tgt1 <*> tcJumpTarget ctx tgt2
tcTermStmt ctx (Return reg) =
  let treg = tcReg ctx reg in
  gget >>>= \st ->
  top_get >>>= \top_st ->
  let tops = stTopVars st
      mb_ret_perms =
        varSubst (permVarSubstOfNames tops) $
        mbSeparate (MNil :>: Proxy) $
        mbValuePermsToDistPerms (stRetPerms top_st) in
  TypedReturn <$>
  pcmRunImplM CruCtxNil
  (const $ TypedRet Refl (stRetType top_st) treg mb_ret_perms)
  (proveVarsImpl $ distPermsToExDistPerms $
   varSubst (singletonVarSubst $ typedRegVar treg) mb_ret_perms)
tcTermStmt ctx (ErrorStmt reg) = greturn $ TypedErrorStmt $ tcReg ctx reg
tcTermStmt _ tstmt =
  error ("tcTermStmt: unhandled termination statement: "
         ++ show (pretty tstmt))


----------------------------------------------------------------------
-- * Permission Checking for Blocks and Sequences of Statements
----------------------------------------------------------------------

-- | Translate and emit a Crucible statement sequence, starting and ending with
-- an empty stack of distinguished permissions
tcEmitStmtSeq :: PermCheckExtC ext => CtxTrans ctx ->
                 StmtSeq ext cblocks ret ctx ->
                 PermCheckM ext cblocks blocks tops ret
                 () RNil
                 (TypedStmtSeq ext blocks tops ret RNil) RNil
                 ()
tcEmitStmtSeq ctx (ConsStmt loc stmt stmts) =
  tcEmitStmt ctx loc stmt >>>= \ctx' -> tcEmitStmtSeq ctx' stmts
tcEmitStmtSeq ctx (TermStmt loc tstmt) =
  tcTermStmt ctx tstmt >>>= \typed_tstmt ->
  gmapRet (>> return (TypedTermStmt loc typed_tstmt))

llvmReprWidth :: ExtRepr (LLVM arch) -> NatRepr (ArchWidth arch)
llvmReprWidth ExtRepr_LLVM = knownRepr

setInputExtState :: ExtRepr ext -> CruCtx as -> MapRList Name as ->
                    PermCheckM ext cblocks blocks tops ret r ps r ps ()
setInputExtState ExtRepr_Unit _ _ = greturn ()
setInputExtState repr@ExtRepr_LLVM tps ns
  | [n] <- findLLVMFrameVars (llvmReprWidth repr) tps ns
  = setFramePtr $ TypedReg n
setInputExtState ExtRepr_LLVM _ _ =
  -- FIXME: make sure there are not more than one frame var and/or a frame var
  -- of the wrong type
  greturn ()

-- | Type-check a single block entrypoint
tcBlockEntry :: PermCheckExtC ext => Bool -> Block ext cblocks ret args ->
                BlockEntryInfo blocks tops ret (CtxToRList args) ->
                TopPermCheckM ext cblocks blocks tops ret
                (TypedEntry ext blocks tops ret (CtxToRList args))
tcBlockEntry is_scc blk (BlockEntryInfo {..}) =
  get >>= \(TopPermCheckState {..}) ->
  let args_prxs = cruCtxProxies entryInfoArgs
      ghosts_prxs = cruCtxProxies $ entryGhosts entryInfoID
      ret_perms =
        mbCombine $ extMbMulti ghosts_prxs $ extMbMulti args_prxs $
        mbSeparate (MNil :>: Proxy) stRetPerms in
  fmap (TypedEntry entryInfoID stTopCtx entryInfoArgs stRetType is_scc
        entryInfoPermsIn ret_perms) $
  liftInnerToTopM $ strongMbM $
  flip nuMultiWithElim1 (mbValuePermsToDistPerms
                         entryInfoPermsIn) $ \ns perms ->
  let (tops_args, ghosts_ns) = splitMapRList Proxy ghosts_prxs ns
      (tops_ns, args_ns) = splitMapRList Proxy args_prxs tops_args
      ctx = mkCtxTrans (blockInputs blk) args_ns in
  runPermCheckM tops_ns (distPermSet perms) $
  setVarTypes ns (appendCruCtx
                  (appendCruCtx stTopCtx entryInfoArgs)
                  (entryGhosts entryInfoID)) >>>
  stmtTraceM (\i ->
               string "Type-checking block" <+> pretty (blockID blk) <>
               comma <+> string "entrypoint" <+> int (entryIndex entryInfoID)
               <> line <>
               string "Input types:"
               <> align (pretty $
                         appendCruCtx (entryGhosts entryInfoID) entryInfoArgs)
               PP.<$>
               string "Input perms:"
               <> align (permPretty i perms)) >>>
  setInputExtState knownRepr (entryGhosts entryInfoID) ghosts_ns >>>
  stmtRecombinePerms >>>
  tcEmitStmtSeq ctx (blk ^. blockStmts)

-- | Type-check a Crucible block
tcBlock :: PermCheckExtC ext => Bool -> Member blocks (CtxToRList args) ->
           Block ext cblocks ret args ->
           TopPermCheckM ext cblocks blocks tops ret
           (TypedBlock ext blocks tops ret (CtxToRList args))
tcBlock is_scc memb blk =
  do entries <- blockInfoEntries <$> mapRListLookup memb <$>
       stBlockInfo <$> get
     TypedBlock <$> mapM (tcBlockEntry is_scc blk) entries

-- | Type-check a Crucible block and put its translation into the 'BlockInfo'
-- for that block. The 'Bool' flag indicates if the block is the head of a
-- strongly-connected component, i.e., if it is the entrypoint of a loop.
tcEmitBlock :: PermCheckExtC ext => Bool -> Block ext cblocks ret args ->
               TopPermCheckM ext cblocks blocks tops ret ()
tcEmitBlock is_scc blk =
  do !memb <- stLookupBlockID (blockID blk) <$> get
     !block_t <- tcBlock is_scc memb blk
     modifyBlockInfo (blockInfoMapSetBlock memb block_t)

-- | Extend permissions on the real arguments of a block to a 'DistPerms' for
-- all the arguments of the block
argPermsToAllPerms :: CruCtx ghosts -> Mb ghosts (MbValuePerms args) ->
                      MbValuePerms (ghosts :++: args)
argPermsToAllPerms ghosts arg_perms =
  fmap (appendValuePerms (trueValuePerms ghosts)) $
  mbCombine arg_perms

-- | Build the input permissions for the initial block of a CFG, where the
-- top-level variables (which in this case are the ghosts plus the normal
-- arguments of the function permission) get the function input permissions and
-- the normal arguments get equality permissions to their respective top-level
-- variables.
funPermToBlockInputs :: FunPerm ghosts args ret ->
                        Mb (ghosts :++: args)
                        (ValuePerms ((ghosts :++: args) :++: args))
funPermToBlockInputs fun_perm =
  let args_prxs = cruCtxProxies $ funPermArgs fun_perm
      ghosts_prxs = cruCtxProxies $ funPermGhosts fun_perm in
  mbCombine $
  flip nuMultiWithElim1 (funPermIns fun_perm) $ \ghosts_ns mb_perms_in ->
  flip nuMultiWithElim1 mb_perms_in $ \args_ns perms_in ->
  appendValuePerms (appendValuePerms
                    (trueValuePerms $ funPermGhosts fun_perm) perms_in)
  (eqValuePerms args_ns)

-- | Type-check a Crucible CFG
tcCFG :: PermCheckExtC ext => PermEnv ->
         FunPerm ghosts (CtxToRList inits) ret ->
         CFG ext blocks inits ret ->
         TypedCFG ext (CtxCtxToRList blocks) ghosts (CtxToRList inits) ret
tcCFG env fun_perm@(FunPerm ghosts inits _ _ _) (cfg :: CFG ext cblocks inits ret) =
  let inits = mkCruCtx $ handleArgTypes $ cfgHandle cfg
      tops = appendCruCtx ghosts inits
      perms_out = argPermsToAllPerms ghosts (funPermOuts fun_perm) in
  flip evalState (emptyTopPermCheckState
                  tops
                  (handleReturnType $ cfgHandle cfg)
                  perms_out
                  (cfgBlockMap cfg) env) $
  do
     -- First, add a block entrypoint for the initial block of the function
     init_memb <- stLookupBlockID (cfgEntryBlockID cfg) <$> get
     let init_entryID = TypedEntryID init_memb CruCtxNil 0
     -- let init_args = mkCruCtx $ handleArgTypes $ cfgHandle cfg
     modifyBlockInfo (addBlockEntry init_memb $
                      BlockEntryInfo init_entryID tops inits
                      (extMbMulti (cruCtxProxies $ funPermArgs fun_perm) $
                       funPermToBlockInputs fun_perm))

     -- Next, add entrypoints for all the block entry hints, keeping track of
     -- the hints that we actually used
     --
     -- FIXME: why does GHC need this type to be given?
     block_entry_hints :: [Some (BlockEntryHint _ inits ret)] <-
       fmap catMaybes $
       forM (lookupBlockEntryHints env cfg) $ \hint -> case hint of
       Some (BlockEntryHint
             _ _ h_blkID h_topargs h_ghosts h_perms_in)
         | Just Refl <- testEquality h_topargs (appendCruCtx ghosts inits) ->
           do h_memb <- stLookupBlockID h_blkID <$> get
              let h_entryID = TypedEntryID h_memb h_ghosts 0
              let h_args = mkCruCtx $ blockInputs (cfgBlockMap cfg !
                                                   blockIDIndex h_blkID)
              let h_allargs = appendCruCtx h_ghosts h_args
              modifyBlockInfo (addBlockEntry h_memb $
                               BlockEntryInfo h_entryID tops h_args h_perms_in)
              return (Just hint)
       _ ->
         -- FIXME HERE NOW: warn the user that the hint did not match
         return Nothing

     -- Visit all the blocks in a weak topological order, meaning that we visit
     -- a block before its successors (the blocks it could jump to) in the CFG.
     -- The exception is that blocks with block entry hints should be visited
     -- first, before any blocks that jump to them. To ensure this, we remove
     -- all links to a block with a block entry hint and then add a dummy start
     -- node, represented by Nothing, that has the function start block and also
     -- all blocks with hints as successors.
     let hint_nodes = map (Just . fmapF blockEntryHintBlockID) block_entry_hints
     let nodeSuccessors (Just node) =
           filter (\node' -> notElem node' hint_nodes) $
           map Just $ cfgSuccessors cfg node
         nodeSuccessors Nothing = Just (cfgStart cfg) : hint_nodes
     !(init_st) <- get
     mapM_ (visit cfg) (trace "visiting CFG..." $
                        weakTopologicalOrdering nodeSuccessors Nothing)
     !final_st <- get
     trace "visiting complete!" $ return $ TypedCFG
       { tpcfgHandle = TypedFnHandle ghosts (cfgHandle cfg)
       , tpcfgFunPerm = fun_perm
       , tpcfgBlockMap =
           mapMapRList
           (maybe (error "tcCFG: unvisited block!") id . blockInfoBlock)
           (stBlockInfo final_st)
       , tpcfgEntryBlockID = init_entryID }
  where
    visit :: PermCheckExtC ext => CFG ext cblocks inits ret ->
             WTOComponent (Maybe (Some (BlockID cblocks))) ->
             TopPermCheckM ext cblocks blocks tops ret ()
    visit cfg (Vertex Nothing) = return ()
    visit cfg (Vertex (Just (Some blkID))) =
      do blkIx <- memberLength <$> stLookupBlockID blkID <$> get
         () <- trace ("Visiting block: " ++ show blkIx) $ return ()
         !ret <- tcEmitBlock False (getBlock blkID (cfgBlockMap cfg))
         !s <- get
         trace ("Visiting block " ++ show blkIx ++ " complete") $ return ret
    visit cfg (SCC (Just (Some blkID)) comps) =
      tcEmitBlock True (getBlock blkID (cfgBlockMap cfg)) >>
      mapM_ (visit cfg) comps
    visit cfg (SCC Nothing comps) =
      -- NOTE: this should never actually happen, as nothing jumps to Nothing
      mapM_ (visit cfg) comps
