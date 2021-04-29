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
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ConstraintKinds #-}
-- {-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Verifier.SAW.Heapster.TypedCrucible where

import Data.Maybe
import qualified Data.Text as Text
import Data.List (find, findIndex)
import Data.Functor.Constant
import Data.Functor.Product
import Data.Type.Equality
import Data.Kind
import qualified Data.BitVector.Sized as BV
import GHC.TypeLits

import What4.ProgramLoc
import What4.FunctionName
import What4.Interface (StringLiteral(..))

import Control.Lens hiding ((:>), Index, ix)
import Control.Monad.State.Strict hiding (ap)
import Control.Monad.Reader hiding (ap)

import Prettyprinter as PP

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind
import Data.Binding.Hobbits.NameSet (NameSet, SomeName(..), SomeRAssign(..),
                                     namesListToNames, namesToNamesList,
                                     nameSetIsSubsetOf)
import qualified Data.Binding.Hobbits.NameSet as NameSet
import Data.Binding.Hobbits.NameMap (NameMap)
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty, take, view, last, drop)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC

import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.Analysis.Fixpoint.Components
import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.Implication

import Debug.Trace


----------------------------------------------------------------------
-- * Handling Crucible Extensions
----------------------------------------------------------------------

-- | A Crucible extension that satisfies 'NuMatching'
type NuMatchingExtC ext =
  (NuMatchingAny1 (ExprExtension ext RegWithVal)
  -- (NuMatchingAny1 (ExprExtension ext TypedReg)
   -- , NuMatchingAny1 (StmtExtension ext TypedReg))
  )

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
permCheckExtStateNames :: PermCheckExtState ext -> Some (RAssign ExprVar)
permCheckExtStateNames (PermCheckExtState_LLVM (Just treg)) =
  Some (MNil :>: typedRegVar treg)
permCheckExtStateNames (PermCheckExtState_LLVM Nothing) = Some MNil
permCheckExtStateNames (PermCheckExtState_Unit) = Some MNil


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
  TypedRegsCons :: !(TypedRegs ctx) -> !(TypedReg a) -> TypedRegs (ctx :> a)

-- | Extract out a sequence of variables from a 'TypedRegs'
typedRegsToVars :: TypedRegs ctx -> RAssign Name ctx
typedRegsToVars TypedRegsNil = MNil
typedRegsToVars (TypedRegsCons regs (TypedReg x)) = typedRegsToVars regs :>: x

-- | Convert a sequence of variables to a 'TypedRegs'
varsToTypedRegs :: RAssign Name ctx -> TypedRegs ctx
varsToTypedRegs MNil = TypedRegsNil
varsToTypedRegs (xs :>: x) = TypedRegsCons (varsToTypedRegs xs) (TypedReg x)

-- | Turn a sequence of typed registers into a variable substitution
typedRegsToVarSubst :: TypedRegs ctx -> PermVarSubst ctx
typedRegsToVarSubst = permVarSubstOfNames . typedRegsToVars

-- | A typed register along with its value if that is known statically
data RegWithVal a
  = RegWithVal (TypedReg a) (PermExpr a)
  | RegNoVal (TypedReg a)

-- | Get the 'TypedReg' from a 'RegWithVal'
regWithValReg :: RegWithVal a -> TypedReg a
regWithValReg (RegWithVal r _) = r
regWithValReg (RegNoVal r) = r

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
  TypedExpr !(App ext RegWithVal tp) !(Maybe (PermExpr tp))

-- | A "typed" function handle is a normal function handle along with a context
-- of ghost variables
data TypedFnHandle ghosts args ret where
  TypedFnHandle :: !(CruCtx ghosts) -> !(FnHandle cargs ret) ->
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


-- | As in standard Crucible, blocks are identified by membership proofs that
-- their input arguments are in the @blocks@ list
type TypedBlockID =
  Member :: RList (RList CrucibleType) -> RList CrucibleType -> Type

-- | All of our blocks have multiple entry points, for different inferred types,
-- so a "typed" 'BlockID' is a normal Crucible 'BlockID' (which is just an index
-- into the @blocks@ context of contexts) plus an 'Int' specifying which entry
-- point to that block
data TypedEntryID blocks args =
  TypedEntryID { entryBlockID :: TypedBlockID blocks args, entryIndex :: Int }
  deriving Eq

-- | Compute the length of a 'Member' proof, which corresponds to its deBruijn
-- index, i.e., number of hops from the right
memberLength :: Member a as -> Int
memberLength Member_Base = 0
memberLength (Member_Step memb) = 1 + memberLength memb

-- | Compute the indices corresponding to the 'BlockID' and 'entryIndex' of a
-- 'TypedEntryID', for printing purposes
entryIDIndices :: TypedEntryID blocks args -> (Int, Int)
entryIDIndices (TypedEntryID memb ix) = (memberLength memb, ix)

instance Show (TypedEntryID blocks args) where
  show entryID = "<entryID " ++ show (entryIDIndices entryID) ++ ">"

instance TestEquality (TypedEntryID blocks) where
  testEquality (TypedEntryID memb1 i1) (TypedEntryID memb2 i2)
    | i1 == i2 = testEquality memb1 memb2
  testEquality _ _ = Nothing

-- | Each call site, that jumps or branches to another block, is identified by
-- the entrypoint it occurs in and the entrypoint it calls, and is associated
-- with the free variables at that call site, each of which could have
-- permissions being passed by the call
data TypedCallSiteID blocks args vars =
  forall args_src.
  TypedCallSiteID { callSiteSrc :: TypedEntryID blocks args_src,
                    callSiteDest :: TypedEntryID blocks args,
                    callSiteVars :: CruCtx vars }

-- | Get the 'TypedBlockID' of the callee of a call site
callSiteDestBlock :: TypedCallSiteID blocks args vars ->
                     TypedBlockID blocks args
callSiteDestBlock = entryBlockID . callSiteDest

instance TestEquality (TypedCallSiteID blocks args) where
  testEquality (TypedCallSiteID
                src1 dest1 vars1) (TypedCallSiteID src2 dest2 vars2)
    | Just Refl <- testEquality src1 src2
    , dest1 == dest2 = testEquality vars1 vars2
  testEquality _ _ = Nothing

-- | Test if the caller of a 'TypedCallSiteID' equals a given entrypoint
callSiteIDCallerEq :: TypedEntryID blocks args_src ->
                      TypedCallSiteID blocks args vars -> Bool
callSiteIDCallerEq entryID (TypedCallSiteID {..}) =
  isJust $ testEquality entryID callSiteSrc

-- | Test if two 'TypedCallSiteID's are "equivalent", meaning they have the same
-- source and destination but possibly different free variables
callSiteIDEquiv :: TypedCallSiteID blocks args vars ->
                   TypedCallSiteID blocks args' vars' -> Bool
callSiteIDEquiv (TypedCallSiteID src1 dest1 _) (TypedCallSiteID src2 dest2 _) =
  isJust (testEquality src1 src2) && isJust (testEquality dest1 dest2)

-- | Test equality of two 'TypedEntryID's with possibly different type arguments
typedCallSiteIDEq :: TypedCallSiteID blocks args vars ->
                     TypedCallSiteID blocks args' vars' ->
                     Maybe (args :~: args', vars :~: vars')
typedCallSiteIDEq (TypedCallSiteID
                   src1 dest1 vars1) (TypedCallSiteID src2 dest2 vars2)
  | isJust (testEquality src1 src2) =
    (,) <$> testEquality dest1 dest2 <*> testEquality vars1 vars2
typedCallSiteIDEq _ _ = Nothing

-- | A typed target for jump and branch statements, where the argument registers
-- (including top-level function arguments and free variables) are given with
-- their permissions as a 'DistPerms'
data TypedJumpTarget blocks tops ps where
     TypedJumpTarget ::
       !(TypedCallSiteID blocks args vars) ->
       !(Proxy tops) -> !(CruCtx args) ->
       !(DistPerms ((tops :++: args) :++: vars)) ->
       TypedJumpTarget blocks tops ((tops :++: args) :++: vars)


$(mkNuMatching [t| forall tp. TypedReg tp |])
$(mkNuMatching [t| forall tp. RegWithVal tp |])
$(mkNuMatching [t| forall ctx. TypedRegs ctx |])

instance NuMatchingAny1 TypedReg where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 RegWithVal where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall ext tp. NuMatchingExtC ext => TypedExpr ext tp |])
$(mkNuMatching [t| forall ghosts args ret. TypedFnHandle ghosts args ret |])
$(mkNuMatching [t| forall blocks args. TypedEntryID blocks args |])
$(mkNuMatching [t| forall blocks args ghosts. TypedCallSiteID blocks args ghosts |])
$(mkNuMatching [t| forall blocks tops ps_in. TypedJumpTarget blocks tops ps_in |])

instance NuMatchingAny1 (TypedJumpTarget blocks tops) where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 (TypedEntryID blocks) where
  nuMatchingAny1Proof = nuMatchingProof

instance Closable (TypedEntryID blocks args) where
  toClosed (TypedEntryID entryBlockID entryIndex) =
    $(mkClosed [| TypedEntryID |])
    `clApply` toClosed entryBlockID `clApply` toClosed entryIndex

instance Liftable (TypedEntryID blocks args) where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable (TypedCallSiteID blocks args vars) where
  toClosed (TypedCallSiteID src dest vars) =
    $(mkClosed [| TypedCallSiteID |])
    `clApply` toClosed src `clApply` toClosed dest `clApply` toClosed vars

instance Liftable (TypedCallSiteID blocks args vars) where
  mbLift = unClosed . mbLift . fmap toClosed


----------------------------------------------------------------------
-- * Typed Crucible Statements
----------------------------------------------------------------------

-- | Typed Crucible statements with the given Crucible syntax extension and the
-- given set of return values
data TypedStmt ext (rets :: RList CrucibleType) ps_in ps_out where

  -- | Assign a pure Crucible expressions to a register, where pure here means
  -- that its translation to SAW will be pure (i.e., no LLVM pointer operations)
  TypedSetReg :: !(TypeRepr tp) -> !(TypedExpr ext tp) ->
                 TypedStmt ext (RNil :> tp) RNil (RNil :> tp)

  -- | Assign a pure permissions expression to a register
  TypedSetRegPermExpr :: !(TypeRepr tp) -> !(PermExpr tp) ->
                         TypedStmt ext (RNil :> tp) RNil (RNil :> tp)

  -- | A function call to the function in register @f@, which must have function
  -- permission @(ghosts). ps_in -o ps_out@, passing the supplied registers for
  -- the @ghosts@ and @args@, where the former must be equal to the supplied
  -- expressions @gexprs@. A call has permissions
  --
  -- > [gexprs/ghosts]ps_in, ghosts1:eq(gexprs1), ..., ghostsn:eq(gexprsn),
  -- > f:((ghosts). ps_in -o ps_out)
  -- > -o
  -- > [gexprs/ghosts]ps_out
  TypedCall :: args ~ CtxToRList cargs =>
               !(TypedReg (FunctionHandleType cargs ret)) ->
               !(FunPerm ghosts args ret) ->
               !(TypedRegs ghosts) -> !(PermExprs ghosts) -> !(TypedRegs args) ->
               TypedStmt ext (RNil :> ret)
               ((ghosts :++: args) :++: ghosts :> FunctionHandleType cargs ret)
               (ghosts :++: args :> ret)

  -- | Assert a boolean condition, printing the given string on failure
  TypedAssert :: !(TypedReg BoolType) -> !(TypedReg (StringType Unicode)) ->
                 TypedStmt ext RNil RNil RNil

  -- | LLVM-specific statement
  TypedLLVMStmt :: !(TypedLLVMStmt (ArchWidth arch) ret ps_in ps_out) ->
                   TypedStmt (LLVM arch) (RNil :> ret) ps_in ps_out


data TypedLLVMStmt w ret ps_in ps_out where
  -- | Assign an LLVM word (i.e., a pointer with block 0) to a register
  --
  -- Type: @. -o ret:eq(word(x))@
  ConstructLLVMWord :: (1 <= w2, KnownNat w2) =>
                       !(TypedReg (BVType w2)) ->
                       TypedLLVMStmt w (LLVMPointerType w2)
                       RNil
                       (RNil :> LLVMPointerType w2)

  -- | Assert that an LLVM pointer is a word, and return 0. This is the typed
  -- version of 'LLVM_PointerBlock' when we know the input is a word, i.e., has
  -- a pointer block value of 0.
  --
  -- Type: @x:eq(word(y)) -o ret:eq(0)@
  AssertLLVMWord :: (1 <= w2, KnownNat w2) =>
                    !(TypedReg (LLVMPointerType w2)) ->
                    !(PermExpr (BVType w2)) ->
                    TypedLLVMStmt w NatType
                    (RNil :> LLVMPointerType w2)
                    (RNil :> NatType)


  -- | Assert that an LLVM pointer is a pointer
  --
  -- Type: @x:is_llvmptr -o .@
  AssertLLVMPtr :: (1 <= w2, KnownNat w2) =>
                   !(TypedReg (LLVMPointerType w2)) ->
                   TypedLLVMStmt w UnitType (RNil :> LLVMPointerType w2) RNil

  -- | Destruct an LLVM word into its bitvector value, which should equal the
  -- given expression
  --
  -- Type: @x:eq(word(e)) -o ret:eq(e)@
  DestructLLVMWord :: (1 <= w2, KnownNat w2) =>
                      !(TypedReg (LLVMPointerType w2)) ->
                      !(PermExpr (BVType w2)) ->
                      TypedLLVMStmt w (BVType w2)
                      (RNil :> LLVMPointerType w2)
                      (RNil :> BVType w2)

  -- | Add an offset to an LLVM value
  --
  -- Type: @. -o ret:eq(x &+ off)@
  OffsetLLVMValue :: (1 <= w2, KnownNat w2) =>
                     !(TypedReg (LLVMPointerType w2)) ->
                     !(PermExpr (BVType w2)) ->
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
  TypedLLVMLoad :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                   !(TypedReg (LLVMPointerType w)) -> !(LLVMFieldPerm w sz) ->
                   !(DistPerms ps) -> !(LifetimeCurrentPerms ps_l) ->
                   TypedLLVMStmt w (LLVMPointerType sz)
                   (ps :> LLVMPointerType w :++: ps_l)
                   (ps :> LLVMPointerType w :> LLVMPointerType sz :++: ps_l)

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
  TypedLLVMStore :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                    !(TypedReg (LLVMPointerType w)) ->
                    !(LLVMFieldPerm w sz) -> !(PermExpr (LLVMPointerType sz)) ->
                    !(DistPerms ps) -> !(LifetimeCurrentPerms ps_l) ->
                    TypedLLVMStmt w UnitType
                    (ps :> LLVMPointerType w :++: ps_l)
                    (ps :> LLVMPointerType w :++: ps_l)

  -- | Allocate an object of the given size on the given LLVM frame, broken into
  -- word-sized fields followed by a field at the end with the remaining size:
  --
  -- Type:
  -- > fp:frame(ps) -o fp:frame(ps,(ret,i)),
  -- >                 ret:ptr((W,0) |-> true, (W,M) |-> true, (W,2*M) |-> true,
  -- >                         ..., (w, (i-1)*M, 8*(sz-(i-1)*M)) |-> true)
  --
  -- where @sz@ is the number of bytes allocated, @M@ is the machine word size in
  -- bytes, and @i@ is the greatest natural number such that @(i-1)*M < sz@
  TypedLLVMAlloca :: (1 <= w, KnownNat w) => !(TypedReg (LLVMFrameType w)) ->
                     !(LLVMFramePerm w) -> !Integer ->
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
  TypedLLVMDeleteFrame :: (1 <= w, KnownNat w) =>
                          !(TypedReg (LLVMFrameType w)) ->
                          !(LLVMFramePerm w) -> !(DistPerms ps) ->
                          TypedLLVMStmt w UnitType (ps :> LLVMFrameType w) RNil

  -- | Typed version of 'LLVM_LoadHandle', that loads the function handle
  -- referred to by a function pointer, assuming we know it has one:
  --
  -- Type: @x:llvm_funptr(p) -o ret:p@
  TypedLLVMLoadHandle :: (1 <= w, KnownNat w) =>
                         !(TypedReg (LLVMPointerType w)) ->
                         !(TypeRepr (FunctionHandleType cargs ret)) ->
                         !(ValuePerm (FunctionHandleType cargs ret)) ->
                         TypedLLVMStmt w (FunctionHandleType cargs ret)
                         (RNil :> LLVMPointerType w)
                         (RNil :> FunctionHandleType cargs ret)

  -- | Typed version of 'LLVM_ResolveGlobal', that resolves a 'GlobalSymbol' to
  -- an LLVM value, assuming it has the given permission in the environment:
  --
  -- Type: @. -o ret:p@
  TypedLLVMResolveGlobal :: (1 <= w, KnownNat w) =>
                            !GlobalSymbol -> !(ValuePerm (LLVMPointerType w)) ->
                            TypedLLVMStmt w (LLVMPointerType w)
                            RNil (RNil :> LLVMPointerType w)

  -- | An if-then-else statement over LLVM values
  TypedLLVMIte :: (1 <= w2, KnownNat w2) =>
                  !(TypedReg BoolType) -> !(TypedReg (LLVMPointerType w2)) ->
                  !(TypedReg (LLVMPointerType w2)) ->
                  TypedLLVMStmt w (LLVMPointerType w2) RNil
                  (RNil :> LLVMPointerType w2)


-- | Return the input permissions for a 'TypedStmt'
typedStmtIn :: TypedStmt ext rets ps_in ps_out -> DistPerms ps_in
typedStmtIn (TypedSetReg _ _) = DistPermsNil
typedStmtIn (TypedSetRegPermExpr _ _) = DistPermsNil
typedStmtIn (TypedCall (TypedReg f) fun_perm ghosts gexprs args) =
  DistPermsCons
  (funPermDistIns fun_perm (typedRegsToVars ghosts) gexprs (typedRegsToVars args))
  f (ValPerm_Conj1 $ Perm_Fun fun_perm)
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
typedLLVMStmtIn (TypedLLVMLoadHandle (TypedReg f) tp p) =
  distPerms1 f (ValPerm_Conj1 $ Perm_LLVMFunPtr tp p)
typedLLVMStmtIn (TypedLLVMResolveGlobal _ _) =
  DistPermsNil
typedLLVMStmtIn (TypedLLVMIte _ _ _) = DistPermsNil

-- | Return the output permissions for a 'TypedStmt'
typedStmtOut :: TypedStmt ext rets ps_in ps_out -> RAssign Name rets ->
                DistPerms ps_out
typedStmtOut (TypedSetReg _ (TypedExpr _ (Just e))) (_ :>: ret) =
  distPerms1 ret (ValPerm_Eq e)
typedStmtOut (TypedSetReg _ (TypedExpr _ Nothing)) (_ :>: ret) =
  distPerms1 ret ValPerm_True
typedStmtOut (TypedSetRegPermExpr _ e) (_ :>: ret) =
  distPerms1 ret (ValPerm_Eq e)
typedStmtOut (TypedCall _ fun_perm ghosts gexprs args) (_ :>: ret) =
  funPermDistOuts fun_perm (typedRegsToVars
                            ghosts) gexprs (typedRegsToVars args :>: ret)
typedStmtOut (TypedAssert _ _) _ = DistPermsNil
typedStmtOut (TypedLLVMStmt llvmStmt) (_ :>: ret) =
  typedLLVMStmtOut llvmStmt ret

-- | Return the output permissions for a 'TypedStmt'
typedLLVMStmtOut :: TypedLLVMStmt w ret ps_in ps_out -> Name ret ->
                    DistPerms ps_out
typedLLVMStmtOut (ConstructLLVMWord (TypedReg x)) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_LLVMWord $ PExpr_Var x)
typedLLVMStmtOut (AssertLLVMWord (TypedReg _) _) ret =
  distPerms1 ret (ValPerm_Eq $ PExpr_Nat 0)
typedLLVMStmtOut (AssertLLVMPtr _) _ = DistPermsNil
typedLLVMStmtOut (DestructLLVMWord (TypedReg _) e) ret =
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
typedLLVMStmtOut (TypedLLVMLoadHandle _ _ p) ret = distPerms1 ret p
typedLLVMStmtOut (TypedLLVMResolveGlobal _ p) ret =
  distPerms1 ret p
typedLLVMStmtOut (TypedLLVMIte _ (TypedReg x1) (TypedReg x2)) ret =
  distPerms1 ret (ValPerm_Or (ValPerm_Eq $ PExpr_Var x1)
                  (ValPerm_Eq $ PExpr_Var x2))


-- | Check that the permission stack of the given permission set matches the
-- input permissions of the given statement, and replace them with the output
-- permissions of the statement
applyTypedStmt :: TypedStmt ext rets ps_in ps_out -> RAssign Name rets ->
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

-- | A permission implication annotated a top-level error message to be printed
-- on failure
data AnnotPermImpl r ps = AnnotPermImpl !String !(PermImpl r ps)

-- | Typed return argument
data TypedRet tops ret ps =
  TypedRet
  !(ps :~: tops :> ret) !(TypeRepr ret) !(TypedReg ret)
  !(Binding ret (DistPerms ps))


-- | Typed Crucible block termination statements
data TypedTermStmt blocks tops ret ps_in where
  -- | Jump to the given jump target
  TypedJump :: !(AnnotPermImpl (TypedJumpTarget blocks tops) ps_in) ->
               TypedTermStmt blocks tops ret ps_in

  -- | Branch on condition: if true, jump to the first jump target, and
  -- otherwise jump to the second jump target
  TypedBr :: !(TypedReg BoolType) ->
             !(AnnotPermImpl (TypedJumpTarget blocks tops) ps_in) ->
             !(AnnotPermImpl (TypedJumpTarget blocks tops) ps_in) ->
             TypedTermStmt blocks tops ret ps_in

  -- | Return from function, providing the return value and also proof that the
  -- current permissions imply the required return permissions
  TypedReturn :: !(AnnotPermImpl (TypedRet tops ret) ps_in) ->
                 TypedTermStmt blocks tops ret ps_in

  -- | Block ends with an error
  TypedErrorStmt :: !(Maybe String) -> !(TypedReg (StringType Unicode)) ->
                    TypedTermStmt blocks tops ret ps_in


-- | A typed sequence of Crucible statements
data TypedStmtSeq ext blocks tops ret ps_in where
  -- | A permission implication step, which modifies the current permission
  -- set. This can include pattern-matches and/or assertion failures.
  TypedImplStmt :: !(AnnotPermImpl (TypedStmtSeq ext blocks tops ret) ps_in) ->
                   TypedStmtSeq ext blocks tops ret ps_in

  -- | Typed version of 'ConsStmt', which binds new variables for the return
  -- value(s) of each statement
  TypedConsStmt :: !ProgramLoc ->
                   !(TypedStmt ext rets ps_in ps_next) ->
                   !(Mb rets (TypedStmtSeq ext blocks tops ret ps_next)) ->
                   TypedStmtSeq ext blocks tops ret ps_in

  -- | Typed version of 'TermStmt', which terminates the current block
  TypedTermStmt :: !ProgramLoc ->
                   !(TypedTermStmt blocks tops ret ps_in) ->
                   TypedStmtSeq ext blocks tops ret ps_in


$(mkNuMatching [t| forall r ps. NuMatchingAny1 r => AnnotPermImpl r ps |])
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
  genSubst s (mbMatch -> [nuMP| TypedReg x |]) = TypedReg <$> genSubst s x

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (RegWithVal tp) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| RegWithVal r e |] ->
      RegWithVal <$> genSubst s r <*> genSubst s e
    [nuMP| RegNoVal r |] -> RegNoVal <$> genSubst s r

instance SubstVar PermVarSubst m =>
         Substable1 PermVarSubst RegWithVal m where
  genSubst1 = genSubst

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedRegs tp) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| TypedRegsNil |] -> return TypedRegsNil
    [nuMP| TypedRegsCons rs r |] ->
      TypedRegsCons <$> genSubst s rs <*> genSubst s r

instance (NuMatchingAny1 r, SubstVar PermVarSubst m,
          Substable1 PermVarSubst r m) =>
         Substable PermVarSubst (AnnotPermImpl r ps) m where
  genSubst s (mbMatch -> [nuMP| AnnotPermImpl err impl |]) =
    AnnotPermImpl (mbLift err) <$> genSubst s impl

instance (PermCheckExtC ext, NuMatchingAny1 f,
          SubstVar PermVarSubst m, Substable1 PermVarSubst f m,
          Substable PermVarSubst (f BoolType) m) =>
         Substable PermVarSubst (App ext f a) m where
  genSubst s mb_expr = case mbMatch mb_expr of
    [nuMP| ExtensionApp _ |] ->
      error "genSubst: unexpected ExtensionApp"
    [nuMP| BaseIsEq tp e1 e2 |] ->
      BaseIsEq (mbLift tp) <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| EmptyApp |] -> return EmptyApp
    [nuMP| BoolLit b |] -> return $ BoolLit $ mbLift b
    [nuMP| Not e |] ->
      Not <$> genSubst1 s e
    [nuMP| And e1 e2 |] ->
      And <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| Or e1 e2 |] ->
      Or <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BoolXor e1 e2 |] ->
      BoolXor <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatLit n |] ->
      return $ NatLit $ mbLift n
    [nuMP| NatLt e1 e2 |] ->
      NatLt <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatLe e1 e2 |] ->
      NatLe <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatEq e1 e2 |] ->
      NatEq <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatAdd e1 e2 |] ->
      NatAdd <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatSub e1 e2 |] ->
      NatSub <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatMul e1 e2 |] ->
      NatMul <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatDiv e1 e2 |] ->
      NatDiv <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| NatMod e1 e2 |] ->
      NatMod <$> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| HandleLit h |] ->
      return $ HandleLit $ mbLift h
    [nuMP| BVUndef w |] ->
      BVUndef <$> genSubst s w
    [nuMP| BVLit w i |] ->
      BVLit <$> genSubst s w <*> return (mbLift i)
    [nuMP| BVConcat w1 w2 e1 e2 |] ->
      BVConcat <$> genSubst s w1 <*> genSubst s w2 <*>
                   genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVTrunc w1 w2 e |] ->
      BVTrunc <$> genSubst s w1 <*> genSubst s w2 <*> genSubst1 s e
    [nuMP| BVZext w1 w2 e |] ->
      BVZext <$> genSubst s w1 <*> genSubst s w2 <*> genSubst1 s e
    [nuMP| BVSext w1 w2 e |] ->
      BVSext <$> genSubst s w1 <*> genSubst s w2 <*> genSubst1 s e
    [nuMP| BVNot w e |] ->
      BVNot <$> genSubst s w <*> genSubst1 s e
    [nuMP| BVAnd w e1 e2 |] ->
      BVAnd <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVOr w e1 e2 |] ->
      BVOr <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVXor w e1 e2 |] ->
      BVXor <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVNeg w e |] ->
      BVNeg <$> genSubst s w <*> genSubst1 s e
    [nuMP| BVAdd w e1 e2 |] ->
      BVAdd <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVSub w e1 e2 |] ->
      BVSub <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVMul w e1 e2 |] ->
      BVMul <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVUdiv w e1 e2 |] ->
      BVUdiv <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVSdiv w e1 e2 |] ->
      BVSdiv <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVUrem w e1 e2 |] ->
      BVUrem <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVSrem w e1 e2 |] ->
      BVSrem <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVUle w e1 e2 |] ->
      BVUle <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVUlt w e1 e2 |] ->
      BVUlt <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVSle w e1 e2 |] ->
      BVSle <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVSlt w e1 e2 |] ->
      BVSlt <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVCarry w e1 e2 |] ->
      BVCarry <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVSCarry w e1 e2 |] ->
      BVSCarry <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVSBorrow w e1 e2 |] ->
      BVSBorrow <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVShl w e1 e2 |] ->
      BVShl <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVLshr w e1 e2 |] ->
      BVLshr <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BVAshr w e1 e2 |] ->
      BVAshr <$> genSubst s w <*> genSubst1 s e1 <*> genSubst1 s e2
    [nuMP| BoolToBV w e |] ->
      BoolToBV <$> genSubst s w <*> genSubst1 s e
    [nuMP| BVNonzero w e |] ->
      BVNonzero <$> genSubst s w <*> genSubst1 s e
    [nuMP| StringLit str_lit |] ->
      return $ StringLit $ mbLift str_lit
    [nuMP| MkStruct tps flds |] ->
      MkStruct (mbLift tps) <$> genSubst s flds
    [nuMP| GetStruct str ix tp |] ->
      GetStruct <$> genSubst1 s str <*> return (mbLift ix) <*> return (mbLift tp)
    [nuMP| SetStruct tps str ix x |] ->
      SetStruct (mbLift tps) <$> genSubst1 s str <*> return (mbLift ix)
                             <*> genSubst1 s x
    _ ->
      error ("genSubst: unhandled Crucible expression construct: "
             ++ mbLift (fmap (show . ppApp (const (pretty "_"))) mb_expr))


instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable PermVarSubst (TypedExpr ext tp) m where
  genSubst s (mbMatch -> [nuMP| TypedExpr app maybe_val |]) =
    TypedExpr <$> genSubst s app <*> genSubst s maybe_val

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedLLVMStmt w tp ps_out ps_in) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| ConstructLLVMWord r |] -> ConstructLLVMWord <$> genSubst s r
    [nuMP| AssertLLVMWord r e |] ->
      AssertLLVMWord <$> genSubst s r <*> genSubst s e
    [nuMP| AssertLLVMPtr r |] ->
      AssertLLVMPtr <$> genSubst s r
    [nuMP| DestructLLVMWord r e |] ->
      DestructLLVMWord <$> genSubst s r <*> genSubst s e
    [nuMP| OffsetLLVMValue r off |] ->
      OffsetLLVMValue <$> genSubst s r <*> genSubst s off
    [nuMP| TypedLLVMLoad r fp ps ps_l |] ->
      TypedLLVMLoad <$> genSubst s r <*> genSubst s fp <*> genSubst s ps <*>
                        genSubst s ps_l
    [nuMP| TypedLLVMStore r fp e ps cur_ps |] ->
      TypedLLVMStore <$> genSubst s r <*> genSubst s fp <*> genSubst s e <*>
                         genSubst s ps <*> genSubst s cur_ps
    [nuMP| TypedLLVMAlloca r fperms i |] ->
      TypedLLVMAlloca <$> genSubst s r <*> genSubst s fperms <*>
                          return (mbLift i)
    [nuMP| TypedLLVMCreateFrame |] -> return TypedLLVMCreateFrame
    [nuMP| TypedLLVMDeleteFrame r fperms perms |] ->
      TypedLLVMDeleteFrame <$> genSubst s r <*> genSubst s fperms <*>
                               genSubst s perms
    [nuMP| TypedLLVMLoadHandle r tp p |] ->
      TypedLLVMLoadHandle <$> genSubst s r <*> return (mbLift tp) <*> genSubst s p
    [nuMP| TypedLLVMResolveGlobal gsym p |] ->
      TypedLLVMResolveGlobal (mbLift gsym) <$> genSubst s p
    [nuMP| TypedLLVMIte r1 r2 r3 |] ->
      TypedLLVMIte <$> genSubst s r1 <*> genSubst s r2 <*> genSubst s r3


instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable PermVarSubst (TypedStmt ext rets ps_in ps_out) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| TypedSetReg tp expr |] ->
      TypedSetReg (mbLift tp) <$> genSubst s expr
    [nuMP| TypedSetRegPermExpr tp expr |] ->
      TypedSetRegPermExpr (mbLift tp) <$> genSubst s expr
    [nuMP| TypedCall f fun_perm ghosts gexprs args |] ->
      TypedCall <$> genSubst s f <*> genSubst s fun_perm <*>
                    genSubst s ghosts <*> genSubst s gexprs <*> genSubst s args
    [nuMP| TypedAssert r1 r2 |] ->
      TypedAssert <$> genSubst s r1 <*> genSubst s r2
    [nuMP| TypedLLVMStmt llvmStmt |] ->
      TypedLLVMStmt <$> genSubst s llvmStmt


instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedRet tops ret ps) m where
  genSubst s (mbMatch -> [nuMP| TypedRet e tp ret mb_perms |]) =
    TypedRet (mbLift e) (mbLift tp) <$> genSubst s ret <*> genSubst s mb_perms

instance SubstVar PermVarSubst m =>
         Substable1 PermVarSubst (TypedRet tops ret) m where
  genSubst1 = genSubst

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedJumpTarget blocks tops ps) m where
  genSubst s (mbMatch -> [nuMP| TypedJumpTarget siteID prx ctx perms |]) =
    TypedJumpTarget (mbLift siteID) (mbLift prx) (mbLift ctx) <$>
    genSubst s perms

instance SubstVar PermVarSubst m =>
         Substable1 PermVarSubst (TypedJumpTarget blocks tops) m where
  genSubst1 = genSubst

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (TypedTermStmt blocks tops ret ps_in) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| TypedJump impl_tgt |] -> TypedJump <$> genSubst s impl_tgt
    [nuMP| TypedBr reg impl_tgt1 impl_tgt2 |] ->
      TypedBr <$> genSubst s reg <*> genSubst s impl_tgt1 <*>
                  genSubst s impl_tgt2
    [nuMP| TypedReturn impl_ret |] ->
      TypedReturn <$> genSubst s impl_ret
    [nuMP| TypedErrorStmt str r |] ->
      TypedErrorStmt (mbLift str) <$> genSubst s r

instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable PermVarSubst (TypedStmtSeq ext blocks tops ret ps_in) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| TypedImplStmt impl_seq |] ->
      TypedImplStmt <$> genSubst s impl_seq
    [nuMP| TypedConsStmt loc stmt mb_seq |] ->
      TypedConsStmt (mbLift loc) <$> genSubst s stmt <*> genSubst s mb_seq
    [nuMP| TypedTermStmt loc term_stmt |] ->
      TypedTermStmt (mbLift loc) <$> genSubst s term_stmt

instance (PermCheckExtC ext, SubstVar PermVarSubst m) =>
         Substable1 PermVarSubst (TypedStmtSeq ext blocks tops ret) m where
  genSubst1 = genSubst


----------------------------------------------------------------------
-- * Typed Control-Flow Graphs
----------------------------------------------------------------------

-- FIXME: remove in-degree stuff

-- | This type characterizes the number and sort of jumps to a 'TypedEntry'
data TypedEntryInDegree
     -- | There are no jumps to the entrypoint
  = EntryInDegree_None
    -- | There is one jump to the entrypoint
  | EntryInDegree_One
    -- | There is more than one jump to the entrypoint
  | EntryInDegree_Many
    -- | The entrypoint is the head of a loop, so has more than one jump to it,
    -- one of which is a back edge
  | EntryInDegree_Loop

-- | "Add" two in-degrees
addInDegrees :: TypedEntryInDegree -> TypedEntryInDegree -> TypedEntryInDegree
addInDegrees EntryInDegree_Loop _ = EntryInDegree_Loop
addInDegrees _ EntryInDegree_Loop = EntryInDegree_Loop
addInDegrees EntryInDegree_None in_deg = in_deg
addInDegrees in_deg EntryInDegree_None = in_deg
addInDegrees _ _ =
  -- The last case is adding 1 or many + 1 or many = many
  EntryInDegree_Many

-- | Add one to an in-degree
incrInDegree :: TypedEntryInDegree -> TypedEntryInDegree
incrInDegree = addInDegrees EntryInDegree_One

-- | Test if an in-degree is at least many
inDegreeIsMulti :: TypedEntryInDegree -> Bool
inDegreeIsMulti EntryInDegree_None = False
inDegreeIsMulti EntryInDegree_One = False
inDegreeIsMulti EntryInDegree_Many = True
inDegreeIsMulti EntryInDegree_Loop = True

-- | Type-level data-kind to indicate a phase of Heapster, which could be
-- type-checking or translation
data HeapsterPhase = TCPhase | TransPhase

type TCPhase = 'TCPhase
type TransPhase = 'TransPhase

-- | A piece of data of type @a@ needed in the translation phase but that could
-- still be being computed in the type-checking phase
type family TransData phase a where
  TransData TCPhase a = Maybe a
  TransData TransPhase a = a

-- | The body of an implication in a call site, which ensures that the
-- permissions are as expected and gives expressions for the ghost variables. It
-- also includes a 'TypedEntryID' for the callee, to make translation easier.
data CallSiteImplRet blocks tops args ghosts ps_out =
  CallSiteImplRet (TypedEntryID blocks args) (CruCtx ghosts)
  ((tops :++: args) :++: ghosts :~: ps_out) (PermExprs ghosts)

$(mkNuMatching [t| forall blocks tops args ghosts ps_out.
                CallSiteImplRet blocks tops args ghosts ps_out |])

instance NuMatchingAny1 (CallSiteImplRet blocks tops args ghosts) where
  nuMatchingAny1Proof = nuMatchingProof

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (CallSiteImplRet
                                 blocks tops args ghosts ps) m where
  genSubst s (mbMatch -> [nuMP| CallSiteImplRet entryID ghosts Refl gexprs |]) =
    CallSiteImplRet (mbLift entryID) (mbLift ghosts) Refl <$>
    genSubst s gexprs

instance SubstVar PermVarSubst m =>
         Substable1 PermVarSubst (CallSiteImplRet
                                  blocks tops args ghosts) m where
  genSubst1 = genSubst


-- | An implication used in a call site, which binds the input variables in an
-- implication of the output variables
newtype CallSiteImpl blocks ps_in tops args ghosts =
  CallSiteImpl (Mb ps_in (AnnotPermImpl
                          (CallSiteImplRet blocks tops args ghosts) ps_in))

-- | The identity implication
idCallSiteImpl :: TypedEntryID blocks args ->
                  CruCtx tops -> CruCtx args -> CruCtx vars ->
                  CallSiteImpl blocks ((tops :++: args) :++: vars) tops args vars
idCallSiteImpl entryID tops args vars =
  let tops_args_prxs = cruCtxProxies (appendCruCtx tops args) in
  CallSiteImpl $ mbCombine $ nuMulti tops_args_prxs $ \_ ->
  nuMulti (cruCtxProxies vars) $ \vars_ns ->
  AnnotPermImpl "" $ PermImpl_Done $
  CallSiteImplRet entryID vars Refl (namesToExprs vars_ns)

-- | A jump / branch to a particular entrypoint
data TypedCallSite phase blocks tops args ghosts vars =
  TypedCallSite
  {
    -- | The ID of this call site
    typedCallSiteID :: TypedCallSiteID blocks args vars,
    -- | The permissions held at the call site
    typedCallSitePerms :: MbValuePerms ((tops :++: args) :++: vars),
    -- | An implication from the call site perms to the input perms of the
    -- entrypoint we are jumping to
    typedCallSiteImpl :: TransData phase (CallSiteImpl
                                          blocks
                                          ((tops :++: args) :++: vars)
                                          tops args ghosts)
  }

-- | Transition a 'TypedEntry' from type-checking to translation phase if its
-- implication has been proved
completeTypedCallSite ::
  TypedCallSite TCPhase blocks tops args ghosts vars ->
  Maybe (TypedCallSite TransPhase blocks tops args ghosts vars)
completeTypedCallSite call_site
  | Just impl <- typedCallSiteImpl call_site
  = Just $ call_site { typedCallSiteImpl = impl }
completeTypedCallSite _ = Nothing

-- | Build a 'TypedCallSite' with no implication
emptyTypedCallSite :: TypedCallSiteID blocks args vars ->
                      MbValuePerms ((tops :++: args) :++: vars) ->
                      TypedCallSite TCPhase blocks tops args ghosts vars
emptyTypedCallSite siteID perms = TypedCallSite siteID perms Nothing

-- | Build a 'TypedCallSite' that uses the identity implication, meaning its
-- @vars@ will equal the @ghosts@ of its entrypoint
idTypedCallSite :: TypedCallSiteID blocks args vars ->
                   CruCtx tops -> CruCtx args ->
                   MbValuePerms ((tops :++: args) :++: vars) ->
                   TypedCallSite TCPhase blocks tops args vars vars
idTypedCallSite siteID tops args perms =
  TypedCallSite siteID perms $ Just $
  idCallSiteImpl (callSiteDest siteID) tops args (callSiteVars siteID)

-- | A single, typed entrypoint to a Crucible block. Note that our blocks
-- implicitly take extra "ghost" arguments, that are needed to express the input
-- and output permissions. The first of these ghost arguments are the top-level
-- inputs to the entire function.
data TypedEntry phase ext blocks tops ret args ghosts =
  TypedEntry
  {
    -- | The identifier for this particular entrypoing
    typedEntryID :: !(TypedEntryID blocks args),
    -- | The top-level arguments to the entire function
    typedEntryTops :: !(CruCtx tops),
    -- | The real arguments to this block
    typedEntryArgs :: !(CruCtx args),
    -- | The return value from the entire function
    typedEntryRet :: !(TypeRepr ret),
    -- | The call sites that jump to this particular entrypoint
    typedEntryCallers :: ![Some (TypedCallSite phase blocks tops args ghosts)],
    -- | The ghost variables for this entrypoint
    typedEntryGhosts :: !(CruCtx ghosts),
    -- | The input permissions for this entrypoint
    typedEntryPermsIn :: !(MbValuePerms ((tops :++: args) :++: ghosts)),
    -- | The output permissions for the function (cached locally)
    typedEntryPermsOut :: !(MbValuePerms (tops :> ret)),
    -- | The type-checked body of the entrypoint
    typedEntryBody :: !(TransData phase
                        (Mb ((tops :++: args) :++: ghosts)
                         (TypedStmtSeq ext blocks tops ret
                          ((tops :++: args) :++: ghosts))))
  }

-- | Test if an entrypoint has in-degree greater than 1
typedEntryHasMultiInDegree :: TypedEntry phase ext blocks tops ret args ghosts ->
                              Bool
typedEntryHasMultiInDegree entry = length (typedEntryCallers entry) > 1

-- | Transition a 'TypedEntry' from type-checking to translation phase if its
-- body is present and all call site implications have been proved
completeTypedEntry ::
  TypedEntry TCPhase ext blocks tops ret args ghosts ->
  Maybe (TypedEntry TransPhase ext blocks tops ret args ghosts)
completeTypedEntry (TypedEntry { .. })
  | Just body <- typedEntryBody
  , Just callers <- mapM (traverseF completeTypedCallSite) typedEntryCallers
  = Just $ TypedEntry { typedEntryBody = body, typedEntryCallers = callers, .. }
completeTypedEntry _ = Nothing

-- | Build an entrypoint from a call site, using that call site's permissions as
-- the entyrpoint input permissions
singleCallSiteEntry :: TypedCallSiteID blocks args vars ->
                       CruCtx tops -> CruCtx args -> TypeRepr ret ->
                       MbValuePerms ((tops :++: args) :++: vars) ->
                       MbValuePerms (tops :> ret) ->
                       TypedEntry TCPhase ext blocks tops ret args vars
singleCallSiteEntry siteID tops args ret perms_in perms_out =
  TypedEntry
  {
    typedEntryID = callSiteDest siteID, typedEntryTops = tops,
    typedEntryArgs = args, typedEntryRet = ret,
    typedEntryCallers = [Some $ idTypedCallSite siteID tops args perms_in],
    typedEntryGhosts = callSiteVars siteID,
    typedEntryPermsIn = perms_in, typedEntryPermsOut = perms_out,
    typedEntryBody = Nothing
  }

-- | Test if an entrypoint contains a call site with the same caller as the
-- supplied call site id, and, if so, return the index in its list of callers
typedEntryCallerIx :: TypedCallSiteID blocks args vars ->
                      TypedEntry phase ext blocks tops ret args ghosts ->
                      Maybe Int
typedEntryCallerIx (TypedCallSiteID
                    { callSiteSrc = callerID }) (typedEntryCallers -> callers) =
  flip findIndex callers $ \(Some site) ->
  callSiteIDCallerEq callerID $ typedCallSiteID site

-- | Test if an entrypoint contains a call site with the given caller
typedEntryHasCaller :: TypedEntryID blocks args_src ->
                       TypedEntry phase ext blocks tops ret args ghosts ->
                       Bool
typedEntryHasCaller callerID (typedEntryCallers -> callers) =
  any (\(Some site) ->
        callSiteIDCallerEq callerID $ typedCallSiteID site) callers

-- | Return the 'TypedCallSite' structure in an entrypoint for a particular call
-- site id, if it exists. Unlike 'typedEntryHasCaller', this requires the site
-- id to have the same variables.
typedEntryCallerSite ::
  TypedCallSiteID blocks args vars ->
  TypedEntry phase ext blocks tops ret args ghosts ->
  Maybe (TypedCallSite phase blocks tops args ghosts vars)
typedEntryCallerSite siteID (typedEntryCallers -> callers) =
  listToMaybe $ flip mapMaybe callers $ \(Some site) ->
  case testEquality (typedCallSiteID site) siteID of
    Just Refl -> Just site
    Nothing -> Nothing


-- | A typed Crucible block is either a join block, meaning that all jumps to it
-- get joined into the same entrypoint, or is a multi-entry block, meaning that
-- each jump to it gets type-checked separately with a different entrypoint
data TypedBlockSort = JoinSort | MultiEntrySort

-- | A typed Crucible block is a list of typed entrypoints to that block
data TypedBlock phase ext blocks tops ret args =
  forall cargs. (CtxToRList cargs ~ args) =>
  TypedBlock
  {
    -- | An identifier for this block
    typedBlockID :: TypedBlockID blocks args,
    -- | The original Crucible block
    typedBlockBlock :: Block ext (RListToCtxCtx blocks) ret cargs,
    -- | What sort of block is this
    typedBlockSort :: TypedBlockSort,
    -- | The entrypoints into this block; note that the 'entryIndex' of each
    -- entrypoint ID should equal the position of its entrypoint in this list
    _typedBlockEntries :: [Some (TypedEntry phase ext blocks tops ret args)]
  }

makeLenses ''TypedBlock

-- | The input argument types of a block
blockArgs :: TypedBlock phase ext blocks tops ret args -> CruCtx args
blockArgs (TypedBlock {..}) = mkCruCtx $ blockInputs typedBlockBlock

-- | The 'Lens' associated with a 'TypedEntryID'. Note that, unlike the standard
-- lens for list elements, it is an error to use a 'TypedEntryID' for an
-- entrypoint that does not exist.
entryByID :: TypedEntryID blocks args ->
             Lens' (TypedBlock phase ext blocks tops ret args)
             (Some (TypedEntry phase ext blocks tops ret args))
entryByID entryID =
  lens
  (\blk -> (blk ^. typedBlockEntries) !! entryIndex entryID)
  (\blk e -> over typedBlockEntries (replaceNth (entryIndex entryID) e) blk)

-- | Build an empty 'TypedBlock' 
emptyBlockOfSort :: Assignment CtxRepr cblocks -> TypedBlockSort ->
                    Block ext cblocks ret cargs ->
                    TypedBlock TCPhase ext (CtxCtxToRList
                                            cblocks) tops ret (CtxToRList cargs)
emptyBlockOfSort cblocks sort blk
  | Refl <- reprReprToCruCtxCtxEq cblocks
  = TypedBlock (indexCtxToMember (size cblocks) $
                blockIDIndex $ blockID blk) blk sort []

-- | Build a block with a user-supplied input permission
emptyBlockForPerms :: Assignment CtxRepr cblocks ->
                      Block ext cblocks ret cargs -> CruCtx tops ->
                      TypeRepr ret -> CruCtx ghosts ->
                      MbValuePerms ((tops :++: CtxToRList cargs) :++: ghosts) ->
                      MbValuePerms (tops :> ret) ->
                      TypedBlock TCPhase ext (CtxCtxToRList
                                              cblocks) tops ret (CtxToRList cargs)
emptyBlockForPerms cblocks blk tops ret ghosts perms_in perms_out
  | Refl <- reprReprToCruCtxCtxEq cblocks
  , blockID <- indexCtxToMember (size cblocks) $ blockIDIndex $ blockID blk
  , args <- mkCruCtx (blockInputs blk) =
    TypedBlock blockID blk JoinSort
    [Some $ TypedEntry {
        typedEntryID = TypedEntryID blockID 0, typedEntryTops = tops,
        typedEntryArgs = args, typedEntryRet = ret,
        typedEntryCallers = [], typedEntryGhosts = ghosts,
        typedEntryPermsIn = perms_in, typedEntryPermsOut = perms_out,
        typedEntryBody = Nothing }]

-- | Transition a 'TypedBlock' from type-checking to translation phase, by
-- making sure that all of data needed for the translation phase is present
completeTypedBlock :: TypedBlock TCPhase ext blocks tops ret args ->
                      Maybe (TypedBlock TransPhase ext blocks tops ret args)
completeTypedBlock (TypedBlock { .. })
  | Just entries <- mapM (traverseF completeTypedEntry) _typedBlockEntries
  = Just $ TypedBlock { _typedBlockEntries = entries, .. }
completeTypedBlock _ = Nothing

-- | Test if an entrypoint ID has a corresponding entrypoint in a block
entryIDInBlock :: TypedEntryID blocks args_src ->
                  TypedBlock phase ext blocks tops ret args -> Bool
entryIDInBlock entryID blk =
  entryIndex entryID < length (blk ^. typedBlockEntries)

-- | Add a new entrypoint to a block, making sure that its 'entryIndex' lines up
-- with its new position in the list of entrypoints in the block
addEntryToBlock :: TypedEntry phase ext blocks tops ret args ghosts ->
                   TypedBlock phase ext blocks tops ret args ->
                   TypedBlock phase ext blocks tops ret args
addEntryToBlock entry blk
  | i <- entryIndex (typedEntryID entry)
  , i == length (blk ^. typedBlockEntries) =
    over typedBlockEntries (++ [Some entry]) blk
addEntryToBlock _ _ = error "addEntryToBlock"

-- | Look up the entrypoint containing a call site for a given caller. If none
-- exists, either return the first entrypoint, if the block has 'JoinSort', or
-- return a new entrypoint not yet in the block if it has 'MultiEntrySort'
entryIDForCaller :: TypedEntryID blocks args_src ->
                    TypedBlock phase ext blocks tops ret args ->
                    TypedEntryID blocks args
entryIDForCaller callerID blk
  | Just (Some entry) <-
      find (\(Some entry) -> typedEntryHasCaller callerID entry)
      (blk ^. typedBlockEntries)
  = typedEntryID entry
entryIDForCaller _ blk@(typedBlockSort -> JoinSort) =
  TypedEntryID (typedBlockID blk) 0
entryIDForCaller _ blk =
  TypedEntryID (typedBlockID blk) (length (blk ^. typedBlockEntries))

-- | Compute the call site for a call to a block from a given entrypoint, using
-- the entrypoint returned by 'entryIDForCaller'
callSiteIDForCall :: TypedEntryID blocks args_src -> CruCtx vars ->
                     TypedBlock phase ext blocks tops ret args ->
                     TypedCallSiteID blocks args vars
callSiteIDForCall callerID vars blk =
  TypedCallSiteID callerID (entryIDForCaller callerID blk) vars


-- | Set the call site in an entrypoint for a particular caller to have the
-- supplied permissions over the supplied variables. If the entrypoint already
-- has a call site for the same caller, replace that call site with a fresh one,
-- unless its permissions are the same, in which case we do nothing and,
-- notably, preserve any implication that is already there. Insert a new call
-- site if the entrypoint does not yet have one for this caller.
entrySetCallSite :: TypedCallSiteID blocks args vars ->
                    MbValuePerms ((tops :++: args) :++: vars) ->
                    TypedEntry TCPhase ext blocks tops ret args ghosts ->
                    TypedEntry TCPhase ext blocks tops ret args ghosts

-- If the caller is already in the list of call sites and already has the
-- right permissions, do nothing
entrySetCallSite siteID perms_in entry
  | Just i <- typedEntryCallerIx siteID entry
  , Some site <- typedEntryCallers entry !! i
  , Just Refl <- testEquality (callSiteVars siteID) (callSiteVars $
                                                     typedCallSiteID site)
  , perms_in == typedCallSitePerms site =
    entry
-- If the caller is in the list of call sites but does not have the right
-- permissions, replace it with a new, empty call site
entrySetCallSite siteID perms_in entry
  | Just i <- typedEntryCallerIx siteID entry =
    entry { typedEntryCallers =
              replaceNth i (Some $ emptyTypedCallSite siteID perms_in)
              (typedEntryCallers entry) }
-- Otherwise, the caller does not already have a call site, so add a new one
entrySetCallSite siteID perms_in entry =
  entry { typedEntryCallers =
            typedEntryCallers entry ++ [Some $
                                        emptyTypedCallSite siteID perms_in] }

-- | Set the call site to a block for a particular caller to have the supplied
-- permissions over the supplied variables, inserting one if it is not there and
-- replacing any that are already there
blockSetCallSite :: TypedCallSiteID blocks args vars ->
                    CruCtx tops -> TypeRepr ret ->
                    MbValuePerms ((tops :++: args) :++: vars) ->
                    MbValuePerms (tops :> ret) ->
                    TypedBlock TCPhase ext blocks tops ret args ->
                    TypedBlock TCPhase ext blocks tops ret args
-- If the call site already has an entrypoint, update it with entrySetCallSite
blockSetCallSite siteID _ _ perms_in _ blk
  | entryIDInBlock (callSiteDest siteID) blk =
    over (entryByID (callSiteDest siteID))
    (fmapF $ entrySetCallSite siteID perms_in) blk
-- If the call site already has an entrypoint, update it with entrySetCallSite
blockSetCallSite siteID tops ret perms_in perms_out blk =
  addEntryToBlock (singleCallSiteEntry
                   siteID tops (blockArgs blk) ret perms_in perms_out) blk


-- | A map assigning a 'TypedBlock' to each 'BlockID'
type TypedBlockMap phase ext blocks tops ret =
  RAssign (TypedBlock phase ext blocks tops ret) blocks

instance Show (TypedEntry phase ext blocks tops ret args ghosts) where
  show (TypedEntry { .. }) =
    "<entry " ++ show (entryIDIndices typedEntryID) ++ ">"

instance Show (TypedBlock phase ext blocks tops ret args) where
  show = concatMap (\(Some entry) -> show entry) . (^. typedBlockEntries)

instance Show (TypedBlockMap phase ext blocks tops ret) where
  show blkMap = show $ RL.mapToList show blkMap

-- | Transition a 'TypedBlockMap' from type-checking to translation phase, by
-- making sure that all of data needed for the translation phase is present
completeTypedBlockMap :: TypedBlockMap TCPhase ext blocks tops ret ->
                         Maybe (TypedBlockMap TransPhase ext blocks tops ret)
completeTypedBlockMap = traverseRAssign completeTypedBlock

-- | Build the input permissions for the initial block of a CFG, where the
-- top-level variables (which in this case are the ghosts plus the normal
-- arguments of the function permission) get the function input permissions and
-- the normal arguments get equality permissions to their respective top-level
-- variables.
funPermToBlockInputs :: FunPerm ghosts args ret ->
                        MbValuePerms ((ghosts :++: args) :++: args)
funPermToBlockInputs fun_perm =
  let args_prxs = cruCtxProxies $ funPermArgs fun_perm in
  extMbMulti args_prxs $
  flip nuMultiWithElim1 (funPermIns fun_perm) $ \ghosts_args_ns perms_in ->
  let (_, args_ns) =
        RL.split (funPermGhosts fun_perm) args_prxs ghosts_args_ns in
  appendValuePerms perms_in (eqValuePerms args_ns)

-- | Build an initial 'TypedBlockMap' from a 'BlockMap'. Determine the sort, and
-- possibly entrypoint permissions, for each block by using hints in the
-- supplied 'PermEnv' along with a list of 'Bool' flags indicating which blocks
-- are at the head of a loop (or other strongly-connected component)
initTypedBlockMap ::
  PermEnv -> FunPerm ghosts (CtxToRList init) ret ->
  CFG ext cblocks init ret -> Assignment (Constant Bool) cblocks ->
  TypedBlockMap TCPhase ext (CtxCtxToRList
                             cblocks) (ghosts :++: CtxToRList init) ret
initTypedBlockMap env fun_perm cfg sccs =
  let block_map = cfgBlockMap cfg
      cblocks = fmapFC blockInputs block_map
      ret = funPermRet fun_perm
      tops = funPermTops fun_perm
      top_perms_in = funPermToBlockInputs fun_perm
      perms_out = funPermOuts fun_perm in
  assignToRListRList
  (\(Pair blk (Constant is_scc)) ->
    let blkID = blockID blk
        hints = lookupBlockHints env (cfgHandle cfg) cblocks blkID in
    case hints of
      _ | Just Refl <- testEquality (cfgEntryBlockID cfg) blkID ->
          emptyBlockForPerms cblocks blk tops ret CruCtxNil top_perms_in perms_out
      (find isBlockEntryHint ->
       Just (BlockEntryHintSort tops' ghosts perms_in))
        | Just Refl <- testEquality tops tops' ->
          emptyBlockForPerms cblocks blk tops ret ghosts perms_in perms_out
      _ | is_scc || any isJoinPointHint hints ->
          emptyBlockOfSort cblocks JoinSort blk
      _ -> emptyBlockOfSort cblocks MultiEntrySort blk) $
  Ctx.zipWith Pair block_map sccs


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
                 !(TypedBlockMap TransPhase ext blocks (ghosts :++: inits) ret)
             , tpcfgEntryID :: !(TypedEntryID blocks inits)
             }

-- | Get the input permissions for a 'CFG'
tpcfgInputPerms :: TypedCFG ext blocks ghosts inits ret ->
                   MbValuePerms (ghosts :++: inits)
tpcfgInputPerms = funPermIns . tpcfgFunPerm

-- | Get the output permissions for a 'CFG'
tpcfgOutputPerms :: TypedCFG ext blocks ghosts inits ret ->
                    MbValuePerms (ghosts :++: inits :> ret)
tpcfgOutputPerms = funPermOuts . tpcfgFunPerm


----------------------------------------------------------------------
-- * Monad(s) for Permission Checking
----------------------------------------------------------------------

-- | A translation of a Crucible context to 'TypedReg's that exist in the local
-- Hobbits context
type CtxTrans ctx = Assignment TypedReg ctx

-- | Build a Crucible context translation from a set of variables
mkCtxTrans :: Assignment f ctx -> RAssign Name (CtxToRList ctx) -> CtxTrans ctx
mkCtxTrans (viewAssign -> AssignEmpty) _ = Ctx.empty
mkCtxTrans (viewAssign -> AssignExtend ctx' _) (ns :>: n) =
  extend (mkCtxTrans ctx' ns) (TypedReg n)

-- | Add a variable to the current Crucible context translation
addCtxName :: CtxTrans ctx -> ExprVar tp -> CtxTrans (ctx ::> tp)
addCtxName ctx x = extend ctx (TypedReg x)


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
    -- | The top-level inputs of the function being type-checked
    stTopCtx :: !(CruCtx tops),
    -- | The return type of the function being type-checked
    stRetType :: !(TypeRepr ret),
    -- | The return permission of the function being type-checked
    stRetPerms :: !(MbValuePerms (tops :> ret)),
    -- | A mapping from 'BlockID's to 'TypedBlockID's
    stBlockTrans :: !(Assignment (BlockIDTrans blocks) cblocks),
    -- | The current set of type-checked blocks
    _stBlockMap :: !(TypedBlockMap TCPhase ext blocks tops ret),
    -- | The permissions environment
    stPermEnv :: !PermEnv,
    -- | The un-translated input types of all of the Crucible blocks
    --
    -- FIXME: this is only needed to look up hints, to prove that the @blocks@
    -- type argument of the hints are equal to that of the function being
    -- type-checked; if we translated @blocks@ to @'CtxCtxToRList' blocks@ when
    -- creating the hints, this field would go away
    stBlockTypes :: !(Assignment CtxRepr cblocks),
    -- | Equality constraint between @cblocks@ and @blocks@
    stCBlocksEq :: RListToCtxCtx blocks :~: cblocks,
    -- | The endianness of the current architecture
    stEndianness :: !EndianForm
  }

makeLenses ''TopPermCheckState

-- | Build an empty 'TopPermCheckState' from a Crucible 'BlockMap'
emptyTopPermCheckState ::
  PermEnv -> FunPerm ghosts (CtxToRList init) ret ->
  EndianForm -> CFG ext cblocks init ret -> Assignment (Constant Bool) cblocks ->
  TopPermCheckState ext cblocks (CtxCtxToRList
                                 cblocks) (ghosts :++: CtxToRList init) ret
emptyTopPermCheckState env fun_perm endianness cfg sccs =
  let blkMap = cfgBlockMap cfg in
  TopPermCheckState
  { stTopCtx = funPermTops fun_perm
  , stRetType = funPermRet fun_perm
  , stRetPerms = funPermOuts fun_perm
  , stBlockTrans = buildBlockIDMap blkMap
  , _stBlockMap = initTypedBlockMap env fun_perm cfg sccs
  , stPermEnv = env
  , stBlockTypes = fmapFC blockInputs blkMap
  , stCBlocksEq = reprReprToCruCtxCtxEq (fmapFC blockInputs blkMap)
  , stEndianness = endianness
  }


-- | Look up a Crucible block id in a top-level perm-checking state
stLookupBlockID :: BlockID cblocks args ->
                   TopPermCheckState ext cblocks blocks tops ret ->
                   TypedBlockID blocks (CtxToRList args)
stLookupBlockID (BlockID ix) st =
  unBlockIDTrans $ stBlockTrans st Ctx.! ix

-- | The top-level monad for permission-checking CFGs
type TopPermCheckM ext cblocks blocks tops ret =
  State (TopPermCheckState ext cblocks blocks tops ret)

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



-- | A change to a 'TypedBlockMap'
data TypedBlockMapDelta blocks tops ret where
  -- | Set the call site to a block for a particular caller to have the supplied
  -- permissions over the supplied variables
  TypedBlockMapSetCallSite :: TypedCallSiteID blocks args vars ->
                              MbValuePerms ((tops :++: args) :++: vars) ->
                              TypedBlockMapDelta blocks tops ret

-- | Apply a 'TypedBlockMapDelta' to a 'TypedBlockMap'
applyTypedBlockMapDelta :: TypedBlockMapDelta blocks tops ret ->
                           TopPermCheckState ext cblocks blocks tops ret ->
                           TopPermCheckState ext cblocks blocks tops ret
applyTypedBlockMapDelta (TypedBlockMapSetCallSite siteID perms_in) top_st =
  over (stBlockMap . member (entryBlockID $ callSiteDest siteID))
  (blockSetCallSite siteID (stTopCtx top_st) (stRetType top_st)
   perms_in (stRetPerms top_st))
  top_st

-- | Apply a list of 'TypedBlockMapDelta's to a 'TopPermCheckState'
applyDeltasToTopState :: [TypedBlockMapDelta blocks tops ret] ->
                         TopPermCheckState ext cblocks blocks tops ret ->
                         TopPermCheckState ext cblocks blocks tops ret
applyDeltasToTopState deltas top_st =
  foldl (flip applyTypedBlockMapDelta) top_st deltas

-- | The state that can be modified by "inner" computations = a list of changes
-- / "deltas" to the current 'TypedBlockMap'
data InnerPermCheckState blocks tops ret =
  InnerPermCheckState
  {
    innerStateDeltas :: [TypedBlockMapDelta blocks tops ret]
  }

-- | Build an empty, closed 'InnerPermCheckState'
clEmptyInnerPermCheckState :: Closed (InnerPermCheckState blocks tops ret)
clEmptyInnerPermCheckState = $(mkClosed [| InnerPermCheckState [] |])


-- | The "inner" monad that runs inside 'PermCheckM' continuations. It can see
-- but not modify the top-level state, but it can add 'TypedBlockMapDelta's to
-- be applied later to the top-level state.
type InnerPermCheckM ext cblocks blocks tops ret =
  ReaderT (TopPermCheckState ext cblocks blocks tops ret)
  (State (Closed (InnerPermCheckState blocks tops ret)))


-- | The local state maintained while type-checking is the current permission
-- set and the permissions required on return from the entire function.
data PermCheckState ext blocks tops ret ps =
  PermCheckState
  {
    stCurPerms  :: !(PermSet ps),
    stExtState  :: !(PermCheckExtState ext),
    stTopVars   :: !(RAssign Name tops),
    stCurEntry  :: !(Some (TypedEntryID blocks)),
    stVarTypes  :: !(NameMap TypeRepr),
    stPPInfo    :: !PPInfo,
    stErrPrefix :: !(Maybe (Doc ()))
  }

-- | Build a default, empty 'PermCheckState'
emptyPermCheckState :: KnownRepr ExtRepr ext => PermSet ps ->
                       RAssign ExprVar tops -> TypedEntryID blocks args ->
                       PermCheckState ext blocks tops ret ps
emptyPermCheckState perms tops entryID =
  PermCheckState { stCurPerms  = perms,
                   stExtState  = emptyPermCheckExtState knownRepr,
                   stTopVars   = tops,
                   stCurEntry  = Some entryID,
                   stVarTypes  = NameMap.empty,
                   stPPInfo    = emptyPPInfo,
                   stErrPrefix = Nothing }

-- | Like the 'set' method of a lens, but allows the @ps@ argument to change
setSTCurPerms :: PermSet ps2 -> PermCheckState ext blocks tops ret ps1 ->
                 PermCheckState ext blocks tops ret ps2
setSTCurPerms perms (PermCheckState {..}) =
  PermCheckState { stCurPerms = perms, .. }

modifySTCurPerms :: (PermSet ps1 -> PermSet ps2) ->
                    PermCheckState ext blocks tops ret ps1 ->
                    PermCheckState ext blocks tops ret ps2
modifySTCurPerms f_perms st = setSTCurPerms (f_perms $ stCurPerms st) st


-- | The generalized monad for permission-checking
type PermCheckM ext cblocks blocks tops ret r1 ps1 r2 ps2 =
  GenStateContM (PermCheckState ext blocks tops ret ps1)
  (InnerPermCheckM ext cblocks blocks tops ret r1)
  (PermCheckState ext blocks tops ret ps2)
  (InnerPermCheckM ext cblocks blocks tops ret r2)

-- | The generalized monad for permission-checking statements
type StmtPermCheckM ext cblocks blocks tops ret ps1 ps2 =
  PermCheckM ext cblocks blocks tops ret
   (TypedStmtSeq ext blocks tops ret ps1) ps1
   (TypedStmtSeq ext blocks tops ret ps2) ps2

-- | Lift an 'InnerPermCheckM' computation to a 'PermCheckM' computation
liftPermCheckM :: InnerPermCheckM ext cblocks blocks tops ret a ->
                  PermCheckM ext cblocks blocks tops ret r ps r ps a
liftPermCheckM m = gcaptureCC $ \k -> m >>= k

-- | Lift an 'InnerPermCheckM' to a 'TopPermCheckM' by applying all the
-- 'TypedBlockMapDelta's generated by the computation
liftInnerToTopM :: InnerPermCheckM ext cblocks blocks tops ret a ->
                   TopPermCheckM ext cblocks blocks tops ret a
liftInnerToTopM m =
  do st <- get
     let (a, cl_inner_st) =
           runState (runReaderT m st) clEmptyInnerPermCheckState
     let deltas = innerStateDeltas $ unClosed cl_inner_st
     modify (applyDeltasToTopState deltas)
     return a

-- | Get the current top-level state modulo the modifications to the current
-- block info map
top_get :: PermCheckM ext cblocks blocks tops ret r ps r ps
           (TopPermCheckState ext cblocks blocks tops ret)
top_get = gcaptureCC $ \k ->
  do top_st <- ask
     deltas <- innerStateDeltas <$> unClosed <$> get
     k $ applyDeltasToTopState deltas top_st

-- | Get the pointer width of the current architecture
llvmReprWidth :: ExtRepr (LLVM arch) -> NatRepr (ArchWidth arch)
llvmReprWidth ExtRepr_LLVM = knownRepr

-- | Set the extension-specific state
setInputExtState :: ExtRepr ext -> CruCtx as -> RAssign Name as ->
                    PermCheckM ext cblocks blocks tops ret r ps r ps ()
setInputExtState ExtRepr_Unit _ _ = greturn ()
setInputExtState repr@ExtRepr_LLVM tps ns
  | [n] <- findLLVMFrameVars (llvmReprWidth repr) tps ns
  = setFramePtr $ TypedReg n
setInputExtState ExtRepr_LLVM _ _ =
  -- FIXME: make sure there are not more than one frame var and/or a frame var
  -- of the wrong type
  greturn ()

-- | Run a 'PermCheckM' computation for a particular entrypoint with a given set
-- of top-level arguments, local arguments, ghost variables, and permissions on
-- all three, and return a result inside a binding for these variables
runPermCheckM ::
  KnownRepr ExtRepr ext => TypedEntryID blocks some_args ->
  CruCtx args -> CruCtx ghosts -> MbValuePerms ((tops :++: args) :++: ghosts) ->
  (RAssign ExprVar tops -> RAssign ExprVar args -> RAssign ExprVar ghosts ->
   DistPerms ((tops :++: args) :++: ghosts) ->
   PermCheckM ext cblocks blocks tops ret () ps_out r ((tops :++: args)
                                                       :++: ghosts) ()) ->
  TopPermCheckM ext cblocks blocks tops ret (Mb ((tops :++: args) :++: ghosts) r)
runPermCheckM entryID args ghosts mb_perms_in m =
  get >>= \(TopPermCheckState {..}) ->
  let args_prxs = cruCtxProxies args
      ghosts_prxs = cruCtxProxies ghosts in
  liftInnerToTopM $ strongMbM $
  flip nuMultiWithElim1 (mbValuePermsToDistPerms mb_perms_in) $ \ns perms_in ->
  let (tops_args, ghosts_ns) = RL.split Proxy ghosts_prxs ns
      (tops_ns, args_ns) = RL.split Proxy args_prxs tops_args
      st = emptyPermCheckState (distPermSet perms_in) tops_ns entryID in
  flip runGenContM (\((), _) -> return ()) $ flip runGenStateT st $
  setVarTypes "top" tops_ns stTopCtx >>>
  setVarTypes "local" args_ns args >>>
  setVarTypes "ghost" ghosts_ns ghosts >>>
  setInputExtState knownRepr ghosts ghosts_ns >>>
  m tops_ns args_ns ghosts_ns perms_in

-- | Emit a 'TypedBlockMapDelta', which must be 'Closed', in an
-- 'InnerPermCheckM' computation
innerEmitDelta :: Closed (TypedBlockMapDelta blocks tops ret) ->
                  InnerPermCheckM ext cblocks blocks tops ret ()
innerEmitDelta cl_delta =
  modify (clApply
          ($(mkClosed [| \delta st ->
                        st { innerStateDeltas =
                               innerStateDeltas st ++ [delta] } |])
           `clApply` cl_delta))

-- | Create a call from the current entrypoint to the specified block, passing
-- the supplied permissions, which must be closed, on local variables
callBlockWithPerms :: TypedEntryID blocks args_src ->
                      TypedBlockID blocks args -> CruCtx vars ->
                      Closed (MbValuePerms ((tops :++: args) :++: vars)) ->
                      InnerPermCheckM ext cblocks blocks tops ret
                      (TypedCallSiteID blocks args vars)
callBlockWithPerms srcEntryID destID vars cl_perms_in =
  do blk <- view (stBlockMap . member destID) <$> ask
     let siteID = callSiteIDForCall srcEntryID vars blk
     innerEmitDelta ($(mkClosed [| TypedBlockMapSetCallSite |])
                    `clApply` toClosed siteID `clApply` cl_perms_in)
     return siteID

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
getPushSimpleRegPerm :: PermCheckExtC ext => TypedReg a ->
                        StmtPermCheckM ext cblocks blocks tops ret
                        (ps :> a) ps (ValuePerm a)
getPushSimpleRegPerm r =
  getRegPerm r >>>= \p_init ->
  pcmEmbedImplM TypedImplStmt emptyCruCtx
  (implPushM (typedRegVar r) p_init >>>
   elimOrsExistsNamesM (typedRegVar r)) >>>= \(_, p_ret) ->
  greturn p_ret

-- | Eliminate any disjunctions, existentials, or recursive permissions for a
-- register and then return the resulting "simple" permission
getSimpleRegPerm :: PermCheckExtC ext => TypedReg a ->
                    StmtPermCheckM ext cblocks blocks tops ret ps ps
                    (ValuePerm a)
getSimpleRegPerm r =
  snd <$> pcmEmbedImplM TypedImplStmt emptyCruCtx (getSimpleVarPerm $
                                                   typedRegVar r)

-- | A version of 'getEqualsExpr' for 'TypedReg's
getRegEqualsExpr ::
  PermCheckExtC ext => TypedReg a ->
  StmtPermCheckM ext cblocks blocks tops ret ps ps (PermExpr a)
getRegEqualsExpr r =
  snd <$> pcmEmbedImplM TypedImplStmt emptyCruCtx (getEqualsExpr $
                                                   PExpr_Var $ typedRegVar r)

-- | Eliminate any disjunctions, existentials, recursive permissions, or
-- equality permissions for an LLVM register until we either get a conjunctive
-- permission for it or we get that it is equal to a bitvector word. In either
-- case, leave the resulting permission on the top of the stack and return its
-- contents as the return value.
getAtomicOrWordLLVMPerms ::
  (1 <= w, KnownNat w, PermCheckExtC ext) => TypedReg (LLVMPointerType w) ->
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
      pcmEmbedImplM TypedImplStmt emptyCruCtx
      (introEqCopyM x (PExpr_Var y) >>> recombinePerm x p) >>>
      getAtomicOrWordLLVMPerms (TypedReg y) >>>= \eith ->
      case eith of
        Left e ->
          pcmEmbedImplM TypedImplStmt emptyCruCtx
          (introCastM x y $ ValPerm_Eq $ PExpr_LLVMWord e) >>>
          greturn (Left e)
        Right ps ->
          pcmEmbedImplM TypedImplStmt emptyCruCtx (introCastM x y $
                                                   ValPerm_Conj ps) >>>
          greturn (Right ps)
    ValPerm_Eq e@(PExpr_LLVMOffset y off) ->
      pcmEmbedImplM TypedImplStmt emptyCruCtx
      (introEqCopyM x e >>> recombinePerm x p) >>>
      getAtomicOrWordLLVMPerms (TypedReg y) >>>= \eith ->
      case eith of
        Left e' ->
          pcmEmbedImplM TypedImplStmt emptyCruCtx (offsetLLVMWordM
                                                   y e' off x) >>>
          greturn (Left $ bvAdd e' off)
        Right ps ->
          pcmEmbedImplM TypedImplStmt emptyCruCtx (castLLVMPtrM
                                                   y (ValPerm_Conj ps) off x) >>>
          greturn (Right $ mapMaybe (offsetLLVMAtomicPerm $ bvNegate off) ps)
    ValPerm_Eq e@(PExpr_LLVMWord e_word) ->
      pcmEmbedImplM TypedImplStmt emptyCruCtx (introEqCopyM x e >>>
                                               recombinePerm x p) >>>
      greturn (Left e_word)
    _ ->
      stmtFailM (\i ->
                  sep [pretty "getAtomicOrWordLLVMPerms:",
                       pretty "Needed atomic permissions for" <+> permPretty i r,
                       pretty "but found" <+>
                       permPretty i p])


-- | Like 'getAtomicOrWordLLVMPerms', but fail if an equality permission to a
-- bitvector word is found
getAtomicLLVMPerms :: (1 <= w, KnownNat w, PermCheckExtC ext) =>
                      TypedReg (LLVMPointerType w) ->
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
                  sep [pretty "getAtomicLLVMPerms:",
                       pretty "Needed atomic permissions for" <+> permPretty i r,
                       pretty "but found" <+>
                       permPretty i (ValPerm_Eq $ PExpr_LLVMWord e)])


-- | Find all the variables of LLVM frame pointer type in a sequence
-- FIXME: move to Permissions.hs
findLLVMFrameVars :: NatRepr w -> CruCtx as -> RAssign Name as ->
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
      stmtTraceM (\i -> pretty "getVarType: could not find type for variable:"
                        <+> permPretty i x) >>>
      error "getVarType"

-- | Look up the types of multiple free variables
getVarTypes :: RAssign Name tps ->
               PermCheckM ext cblocks blocks tops ret r ps r ps (CruCtx tps)
getVarTypes MNil = greturn CruCtxNil
getVarTypes (xs :>: x) = CruCtxCons <$> getVarTypes xs <*> getVarType x

-- | Remember the type of a free variable, and ensure that it has a permission
setVarType :: String -> ExprVar a -> TypeRepr a ->
              PermCheckM ext cblocks blocks tops ret r ps r ps ()
setVarType str x tp =
  gmodify $ \st ->
  st { stCurPerms = initVarPerm x (stCurPerms st),
       stVarTypes = NameMap.insert x tp (stVarTypes st),
       stPPInfo = ppInfoAddExprName str x (stPPInfo st) }

-- | Remember the types of a sequence of free variables
setVarTypes :: String -> RAssign Name tps -> CruCtx tps ->
               PermCheckM ext cblocks blocks tops ret r ps r ps ()
setVarTypes _ _ CruCtxNil = greturn ()
setVarTypes str (xs :>: x) (CruCtxCons tps tp) =
  setVarTypes str xs tps >>> setVarType str x tp

-- | Get the current 'PPInfo'
permGetPPInfo :: PermCheckM ext cblocks blocks tops ret r ps r ps PPInfo
permGetPPInfo = stPPInfo <$> get

-- | Get the current prefix string to give context to error messages
getErrorPrefix :: PermCheckM ext cblocks blocks tops ret r ps r ps (Doc ())
getErrorPrefix = maybe emptyDoc id <$> stErrPrefix <$> gget

-- | Emit debugging output using the current 'PPInfo'
stmtTraceM :: (PPInfo -> Doc ()) ->
              PermCheckM ext cblocks blocks tops ret r ps r ps String
stmtTraceM f =
  (f <$> permGetPPInfo) >>>= \doc ->
  let str = renderDoc doc in
  trace str (greturn str)

-- | Failure in the statement permission-checking monad
stmtFailM :: (PPInfo -> Doc ()) -> PermCheckM ext cblocks blocks tops ret r1 ps1
             (TypedStmtSeq ext blocks tops ret ps2) ps2 a
stmtFailM msg =
  getErrorPrefix >>>= \err_prefix ->
  stmtTraceM (\i -> err_prefix <> line <>
                    pretty "Type-checking failure:" <> softline <> msg i) >>>= \str ->
  gabortM (return $ TypedImplStmt $ AnnotPermImpl str $
           PermImpl_Step (Impl1_Fail "") MbPermImpls_Nil)

-- | FIXME HERE: Make 'ImplM' quantify over any underlying monad, so that we do
-- not have to use 'traversePermImpl' after we run an 'ImplM'
data WithImplState vars a ps ps' =
  WithImplState a (ImplState vars ps) (ps' :~: ps)

-- | Run a 'PermCheckM' computation in a locally-scoped way, where all effects
-- are restricted to the local computation. This is essentially a form of the
-- @reset@ operation of delimited continuations.
--
-- FIXME: this is not used, but is still here in case we need it later...
localPermCheckM ::
  PermCheckM ext cblocks blocks tops ret r_out ps_out r_in ps_in r_out ->
  PermCheckM ext cblocks blocks tops ret r' ps_in r' ps_in r_in
localPermCheckM m =
  gget >>>= \st ->
  liftPermCheckM (runGenContM (runGenStateT m st) (return . fst))

-- | Call 'runImplM' in the 'PermCheckM' monad
pcmRunImplM ::
  CruCtx vars -> Doc () -> (a -> r ps_out) ->
  ImplM vars (InnerPermCheckState blocks tops ret) r ps_out ps_in a ->
  PermCheckM ext cblocks blocks tops ret r' ps_in r' ps_in
  (AnnotPermImpl r ps_in)
pcmRunImplM vars fail_doc retF impl_m =
  getErrorPrefix >>>= \err_prefix ->
  (stCurPerms <$> gget) >>>= \perms_in ->
  (stPermEnv <$> top_get) >>>= \env ->
  (stPPInfo <$> gget) >>>= \ppInfo ->
  (stVarTypes <$> gget) >>>= \varTypes ->
  liftPermCheckM $ lift $
  fmap (AnnotPermImpl (renderDoc (err_prefix <> line <> fail_doc))) $
  runImplM vars perms_in env ppInfo "" True varTypes
  (return . retF . fst) impl_m

-- | Call 'runImplImplM' in the 'PermCheckM' monad
pcmRunImplImplM ::
  CruCtx vars -> Doc () ->
  ImplM vars (InnerPermCheckState blocks tops ret) r ps_out ps_in (PermImpl
                                                                   r ps_out) ->
  PermCheckM ext cblocks blocks tops ret r' ps_in r' ps_in
  (AnnotPermImpl r ps_in)
pcmRunImplImplM vars fail_doc impl_m =
  getErrorPrefix >>>= \err_prefix ->
  (stCurPerms <$> gget) >>>= \perms_in ->
  (stPermEnv <$> top_get) >>>= \env ->
  (stPPInfo <$> gget) >>>= \ppInfo ->
  (stVarTypes <$> gget) >>>= \varTypes ->
  liftPermCheckM $ lift $
  fmap (AnnotPermImpl (renderDoc (err_prefix <> line <> fail_doc))) $
  runImplImplM vars perms_in env ppInfo "" True varTypes impl_m

-- | Embed an implication computation inside a permission-checking computation,
-- also supplying an overall error message for failures
pcmEmbedImplWithErrM ::
  (forall ps. AnnotPermImpl r ps -> r ps) -> CruCtx vars -> Doc () ->
  ImplM vars (InnerPermCheckState blocks tops ret) r ps_out ps_in a ->
  PermCheckM ext cblocks blocks tops ret (r ps_out) ps_out (r ps_in) ps_in
  (PermSubst vars, a)
pcmEmbedImplWithErrM f_impl vars fail_doc m =
  getErrorPrefix >>>= \err_prefix ->
  gmapRet ((f_impl . AnnotPermImpl (renderDoc
                                    (err_prefix <> line <> fail_doc))) <$>) >>>
  (stCurPerms <$> gget) >>>= \perms_in ->
  (stPermEnv <$> top_get) >>>= \env ->
  (stPPInfo <$> gget) >>>= \ppInfo ->
  (stVarTypes <$> gget) >>>= \varTypes ->
  (gcaptureCC $ \k ->
    ask >>= \r ->
    lift $
    runImplM vars perms_in env ppInfo "" True varTypes
    (flip runReaderT r . k) m) >>>= \(a, implSt) ->
  gmodify ((\st -> st { stPPInfo = implSt ^. implStatePPInfo,
                        stVarTypes = implSt ^. implStateNameTypes })
           . setSTCurPerms (implSt ^. implStatePerms)) >>>
  greturn (completePSubst vars (implSt ^. implStatePSubst), a)

-- | Embed an implication computation inside a permission-checking computation
pcmEmbedImplM ::
  (forall ps. AnnotPermImpl r ps -> r ps) -> CruCtx vars ->
  ImplM vars (InnerPermCheckState blocks tops ret) r ps_out ps_in a ->
  PermCheckM ext cblocks blocks tops ret (r ps_out) ps_out (r ps_in) ps_in
  (PermSubst vars, a)
pcmEmbedImplM f_impl vars m = pcmEmbedImplWithErrM f_impl vars mempty m

-- | Special case of 'pcmEmbedImplM' for a statement type-checking context where
-- @vars@ is empty
stmtEmbedImplM ::
  ImplM RNil (InnerPermCheckState
              blocks tops ret) (TypedStmtSeq ext blocks tops ret) ps_out ps_in a ->
  StmtPermCheckM ext cblocks blocks tops ret ps_out ps_in a
stmtEmbedImplM m =
  pcmEmbedImplM TypedImplStmt emptyCruCtx m >>>= \(_,a) -> greturn a

-- | Recombine any outstanding distinguished permissions back into the main
-- permission set, in the context of type-checking statements
stmtRecombinePerms ::
  PermCheckExtC ext => StmtPermCheckM ext cblocks blocks tops ret RNil ps_in ()
stmtRecombinePerms =
  gget >>>= \(!st) ->
  let dist_perms = view distPerms (stCurPerms st) in
  pcmEmbedImplM TypedImplStmt emptyCruCtx (recombinePerms dist_perms) >>>
  greturn ()

-- | Prove a sequence of permissions over some existential variables and append
-- them to the top of the stack
stmtProvePermsAppend :: PermCheckExtC ext =>
                        CruCtx vars -> ExDistPerms vars ps ->
                        StmtPermCheckM ext cblocks blocks tops ret
                        (ps_in :++: ps) ps_in (PermSubst vars)
stmtProvePermsAppend vars ps =
  permGetPPInfo >>>= \ppInfo ->
  let err = pretty "Could not prove" <+> permPretty ppInfo ps in
  pcmEmbedImplWithErrM TypedImplStmt vars err (proveVarsImplAppend
                                               ps) >>>= \(s,_) ->
  greturn s

-- | Prove a sequence of permissions over some existential variables in the
-- context of the empty permission stack
stmtProvePerms :: PermCheckExtC ext =>
                  CruCtx vars -> ExDistPerms vars ps ->
                  StmtPermCheckM ext cblocks blocks tops ret
                  ps RNil (PermSubst vars)
stmtProvePerms vars ps =
  permGetPPInfo >>>= \ppInfo ->
  let err = pretty "Could not prove" <+> permPretty ppInfo ps in
  pcmEmbedImplWithErrM TypedImplStmt vars err (proveVarsImpl ps) >>>= \(s,_) ->
  greturn s

-- | Prove a sequence of permissions over some existential variables in the
-- context of the empty permission stack, but first generate fresh lifetimes for
-- any existential lifetime variables
stmtProvePermsFreshLs :: PermCheckExtC ext =>
                         CruCtx vars -> ExDistPerms vars ps ->
                         StmtPermCheckM ext cblocks blocks tops ret
                         ps RNil (PermSubst vars)
stmtProvePermsFreshLs vars ps =
  permGetPPInfo >>>= \ppInfo ->
  let err = pretty "Could not prove" <+> permPretty ppInfo ps in
  pcmEmbedImplWithErrM TypedImplStmt vars err (instantiateLifetimeVars ps >>>
                                               proveVarsImpl ps) >>>= \(s,_) ->
  greturn s

-- | Prove a single permission in the context of type-checking statements
stmtProvePerm :: (PermCheckExtC ext, KnownRepr CruCtx vars) =>
                 TypedReg a -> Mb vars (ValuePerm a) ->
                 StmtPermCheckM ext cblocks blocks tops ret
                 (ps :> a) ps (PermSubst vars)
stmtProvePerm (TypedReg x) mb_p =
  permGetPPInfo >>>= \ppInfo ->
  let err =
        pretty "Could not prove" <+>
        permPretty ppInfo (fmap (distPerms1 x) mb_p) in
  pcmEmbedImplWithErrM TypedImplStmt knownRepr err (proveVarImpl
                                                    x mb_p) >>>= \(s,_) ->
  greturn s

-- | Try to prove that a register equals a constant integer (of the given input
-- type) using equality permissions in the context
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
  helper (PExpr_Nat i) = greturn (Just $ toInteger i)
  helper (PExpr_BV factors (BV.BV off)) =
    foldM (\maybe_res (BVFactor (BV.BV i) x) ->
            helper (PExpr_Var x) >>= \maybe_x_val ->
            case (maybe_res, maybe_x_val) of
              (Just res, Just x_val) ->
                return (Just (res + x_val * i))
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


-- | Convert a register of one type to one of another type, if possible
convertRegType :: PermCheckExtC ext => ExtRepr ext -> ProgramLoc ->
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
    -- FIXME: should this use endianness?
    -- (stEndianness <$> top_get) >>>= \endianness ->
    withKnownNat w2 $
    emitStmt knownRepr loc (TypedSetReg tp2 $
                            TypedExpr (BVSext w2 w1 $ RegNoVal reg)
                            Nothing) >>>= \(_ :>: x) ->
    stmtRecombinePerms >>>
    greturn (TypedReg x)
convertRegType ExtRepr_LLVM loc reg (LLVMPointerRepr w1) (BVRepr w2)
  | Just Refl <- testEquality w1 w2 =
    withKnownNat w1 $
    stmtProvePerm reg (llvmExEqWord w1) >>>= \sbst ->
    let e = substLookup sbst Member_Base in
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
  stmtFailM (\i -> pretty "Could not cast" <+> permPretty i x
                   <+> pretty "from" <+> pretty (show tp1)
                   <+> pretty "to" <+> pretty (show tp2))


-- | Extract the bitvector of size @sz@ at offset @off@ from a larger bitvector
-- @bv@, using the current endianness to determine how this extraction works
extractBVBytes :: (1 <= w, KnownNat w, PermCheckExtC (LLVM arch)) =>
                  ProgramLoc -> NatRepr sz -> Bytes -> TypedReg (BVType w) ->
                  StmtPermCheckM (LLVM arch) cblocks blocks tops ret RNil RNil
                  (TypedReg (BVType sz))
extractBVBytes loc sz off_bytes (reg :: TypedReg (BVType w)) =
  let w :: NatRepr w = knownNat in
  (stEndianness <$> top_get) >>>= \endianness ->
  withKnownNat sz $
  case (endianness, decideLeq (knownNat @1) sz) of

    -- For little endian, we can just call BVSelect
    (LittleEndian, Left sz_pf)
      | Just (Some off) <- someNat (bytesToBits off_bytes)
      , Left off_sz_w_pf <- decideLeq (addNat off sz) w ->
        withLeqProof sz_pf $ withLeqProof off_sz_w_pf $
        emitStmt knownRepr loc (TypedSetReg (BVRepr sz) $
                                  TypedExpr (BVSelect off sz w $ RegNoVal reg)
                                  Nothing) >>>= \(_ :>: x) ->
        stmtRecombinePerms >>>
        greturn (TypedReg x)

    -- For big endian, we call BVSelect with idx = w - off - sz
    (BigEndian, Left sz_pf)
      | Just (Some idx) <- someNat (intValue w
                                    - toInteger (bytesToBits off_bytes)
                                    - intValue sz)
      , Left idx_sz_w_pf <- decideLeq (addNat idx sz) w ->
        withLeqProof sz_pf $ withLeqProof idx_sz_w_pf $
        emitStmt knownRepr loc (TypedSetReg (BVRepr sz) $
                                TypedExpr (BVSelect idx sz w $ RegNoVal reg)
                                Nothing) >>>= \(_ :>: x) ->
        stmtRecombinePerms >>>
        greturn (TypedReg x)
    _ -> error "extractBVBytes: negative offset!"


-- | Emit a statement in the current statement sequence, where the supplied
-- function says how that statement modifies the current permissions, given the
-- freshly-bound names for the return values. Return those freshly-bound names
-- for the return values.
emitStmt :: CruCtx rets -> ProgramLoc ->
            TypedStmt ext rets ps_in ps_out ->
            StmtPermCheckM ext cblocks blocks tops ret ps_out ps_in
            (RAssign Name rets)
emitStmt tps loc stmt =
  gopenBinding
  ((TypedConsStmt loc stmt <$>) . strongMbM)
  (mbPure (cruCtxProxies tps) ()) >>>= \(ns, ()) ->
  setVarTypes "x" ns tps >>>
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
  mkProgramLoc (functionNameFromText (Text.pack "None"))
  (OtherPos (Text.pack "(Generated by permission type-checker)"))


----------------------------------------------------------------------
-- * Permission Checking and Pretty-Printing for Registers
----------------------------------------------------------------------

-- | Type-check a Crucible register by looking it up in the translated context
tcReg :: CtxTrans ctx -> Reg ctx tp -> TypedReg tp
tcReg ctx (Reg ix) = ctx ! ix

-- | Type-check a Crucible register and also look up its value, if known
tcRegWithVal :: PermCheckExtC ext => CtxTrans ctx -> Reg ctx tp ->
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
tcRegs _ctx (viewAssign -> AssignEmpty) = TypedRegsNil
tcRegs ctx (viewAssign -> AssignExtend regs reg) =
  TypedRegsCons (tcRegs ctx regs) (tcReg ctx reg)

-- | Pretty-print the permissions that are "relevant" to a register, which
-- includes its permissions and all those relevant to any register it is equal
-- to, possibly plus some offset
ppRelevantPerms :: TypedReg tp ->
                   PermCheckM ext cblocks blocks tops ret r ps r ps (Doc ())
ppRelevantPerms r =
  getRegPerm r >>>= \p ->
  permGetPPInfo >>>= \ppInfo ->
  let pp_r = permPretty ppInfo r <> colon <> permPretty ppInfo p in
  case p of
    ValPerm_Eq (PExpr_Var x) ->
      ((pp_r <> comma) <+>) <$> ppRelevantPerms (TypedReg x)
    ValPerm_Eq (PExpr_LLVMOffset x _) ->
      ((pp_r <> comma) <+>) <$> ppRelevantPerms (TypedReg x)
    ValPerm_Eq (PExpr_LLVMWord (PExpr_Var x)) ->
      ((pp_r <> comma) <+>) <$> ppRelevantPerms (TypedReg x)
    _ -> greturn pp_r

-- | Pretty-print a Crucible 'Reg' and what 'TypedReg' it is equal to, along
-- with the relevant permissions for that 'TypedReg'
ppCruRegAndPerms :: CtxTrans ctx -> Reg ctx a ->
                    PermCheckM ext cblocks blocks tops ret r ps r ps (Doc ())
ppCruRegAndPerms ctx r =
  permGetPPInfo >>>= \ppInfo ->
  ppRelevantPerms (tcReg ctx r) >>>= \doc ->
  greturn (PP.group (pretty r <+> pretty '=' <+> permPretty ppInfo (tcReg ctx r)
                     <> comma <+> doc))

-- | Get the permissions on the variables in the input set, the variables in
-- their permissions, the variables in those permissions etc., as in
-- 'varPermsTransFreeVars'
getRelevantPerms :: [SomeName CrucibleType] ->
                    PermCheckM ext cblocks blocks tops ret r ps r ps 
                      (Some DistPerms)
getRelevantPerms (namesListToNames -> SomeRAssign ns) =
  stCurPerms <$> gget >>>= \perms ->
  case varPermsTransFreeVars ns perms of
    Some all_ns -> greturn (Some $ varPermsMulti (RL.append ns all_ns) perms)

-- | Pretty-print a list of Crucible registers and the variables they translate
-- to, and then pretty-print the permissions on those variables and all
-- variables they contain, as well as the top-level input variables and the
-- extension-specific variables
ppCruRegsAndTopsPerms :: CtxTrans ctx -> [Some (Reg ctx)] ->
                         PermCheckM ext cblocks blocks tops ret r ps r ps (Doc (), Doc ())
ppCruRegsAndTopsPerms ctx regs =
  permGetPPInfo >>>= \ppInfo ->
  (stTopVars <$> gget) >>>= \tops ->
  (permCheckExtStateNames <$> stExtState <$> gget) >>>= \(Some ext_ns) ->
  let vars_pp =
        fillSep $ punctuate comma $
        map (\case Some r ->
                     pretty r <+> pretty '=' <+>
                     permPretty ppInfo (tcReg ctx r)) regs
      vars =
        namesToNamesList tops ++ namesToNamesList ext_ns ++
        map (\(Some r) -> SomeName $ typedRegVar $ tcReg ctx r) regs in
  getRelevantPerms vars >>>= \some_perms ->
  case some_perms of
    Some perms -> greturn (vars_pp, permPretty ppInfo perms)

-- | Set the current prefix string to give context to error messages
setErrorPrefix :: ProgramLoc -> Doc () -> CtxTrans ctx -> [Some (Reg ctx)] ->
                  PermCheckM ext cblocks blocks tops ret r ps r ps ()
setErrorPrefix loc stmt_pp ctx regs =
  ppCruRegsAndTopsPerms ctx regs >>>= \(regs_pp, perms_pp) ->
  let prefix =
        PP.sep
        [PP.group (pretty "At" <+> ppShortFileName (plSourceLoc loc)
                  <+> parens stmt_pp),
         PP.group (pretty "Regs:" <+> regs_pp),
         PP.group (pretty "Input perms:" <+> perms_pp)] in
  gmodify $ \st -> st { stErrPrefix = Just prefix }


----------------------------------------------------------------------
-- * Permission Checking for Expressions and Statements
----------------------------------------------------------------------

-- | Get a dynamic representation of an architecture's width
archWidth :: KnownNat (ArchWidth arch) => f arch -> NatRepr (ArchWidth arch)
archWidth _ = knownNat

-- | Type-check a Crucibe block id into a 'TypedBlockID'
tcBlockID :: BlockID cblocks args ->
             StmtPermCheckM ext cblocks blocks tops ret ps ps
             (TypedBlockID blocks (CtxToRList args))
tcBlockID blkID = stLookupBlockID blkID <$> top_get

-- | Type-check a Crucible expression to test if it has a statically known
-- 'PermExpr' value that we can use as an @eq(e)@ permission on the output of
-- the expression
tcExpr :: PermCheckExtC ext => App ext RegWithVal tp ->
          StmtPermCheckM ext cblocks blocks tops ret ps ps
          (Maybe (PermExpr tp))
tcExpr (ExtensionApp _e_ext :: App ext RegWithVal tp)
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = error "tcExpr: unexpected LLVM expression"

-- Equality expressions --

-- For equalities, we can definitely return True if the values of the two
-- expressions being compared are equal, but we can only return False if we know
-- for sure that the two values are unequal. If, e.g., one is a variable with
-- unknown value, it could equal anything, so we know nothing about the result
-- of the equality test.
tcExpr (BoolEq (RegWithVal _ (PExpr_Bool b1))
        (RegWithVal _ (PExpr_Bool b2))) =
  greturn $ Just $ PExpr_Bool (b1 == b2)
tcExpr (BoolEq rwv1 rwv2)
  | regWithValExpr rwv1 == regWithValExpr rwv2 =
    greturn $ Just $ PExpr_Bool True
tcExpr (NatEq (RegWithVal _ (PExpr_Nat i1))
        (RegWithVal _ (PExpr_Nat i2))) =
  greturn $ Just $ PExpr_Bool (i1 == i2)
tcExpr (NatEq rwv1 rwv2)
  | regWithValExpr rwv1 == regWithValExpr rwv2 =
    greturn $ Just $ PExpr_Bool True
tcExpr (BVEq _ (RegWithVal _ bv1) (RegWithVal _ bv2))
  | bvEq bv1 bv2 = greturn $ Just $ PExpr_Bool True
tcExpr (BVEq _ (RegWithVal _ bv1) (RegWithVal _ bv2))
  | not (bvCouldEqual bv1 bv2) = greturn $ Just $ PExpr_Bool False
tcExpr (BVEq _ rwv1 rwv2)
  | regWithValExpr rwv1 == regWithValExpr rwv2 =
    greturn $ Just $ PExpr_Bool True
tcExpr (BaseIsEq _ rwv1 rwv2)
  | regWithValExpr rwv1 == regWithValExpr rwv2 =
    greturn $ Just $ PExpr_Bool True

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

tcExpr (NatLit i) = greturn $ Just $ PExpr_Nat i

-- Bitvector expressions --

tcExpr (BVUndef _w) =
  -- "Undefined" bitvectors are translated to 0 as a stand-in but we don't
  -- return any equality permissions about them
  greturn Nothing

tcExpr (BVLit w (BV.BV i)) = withKnownNat w $ greturn $ Just $ bvInt i

tcExpr (BVSext w2 _ (RegWithVal _ (bvMatchConstInt -> Just i))) =
  withKnownNat w2 $ greturn $ Just $ bvInt i

tcExpr (BVAdd w (RegWithVal _ e1) (RegWithVal _ e2)) =
  withKnownNat w $ greturn $ Just $ bvAdd e1 e2

tcExpr (BVMul w (RegWithVal _ (bvMatchConstInt -> Just i)) (RegWithVal _ e)) =
  withKnownNat w $ greturn $ Just $ bvMult i e
tcExpr (BVMul w (RegWithVal _ e) (RegWithVal _ (bvMatchConstInt -> Just i))) =
  withKnownNat w $ greturn $ Just $ bvMult i e

tcExpr (BoolToBV w (RegWithVal _ (PExpr_Bool True))) =
  withKnownNat w $ greturn $ Just $ bvInt 1
tcExpr (BoolToBV w (RegWithVal _ (PExpr_Bool False))) =
  withKnownNat w $ greturn $ Just $ bvInt 0

tcExpr (BVUlt _ (RegWithVal _ e1) (RegWithVal _ e2))
  | bvLt e1 e2 = greturn $ Just $ PExpr_Bool True
tcExpr (BVUlt _ (RegWithVal _ e1) (RegWithVal _ e2))
  | not (bvCouldBeLt e1 e2) = greturn $ Just $ PExpr_Bool False
tcExpr (BVUle _ (RegWithVal _ e1) (RegWithVal _ e2))
  | bvLt e2 e1 = greturn $ Just $ PExpr_Bool False
tcExpr (BVUle _ (RegWithVal _ e1) (RegWithVal _ e2))
  | not (bvCouldBeLt e2 e1) = greturn $ Just $ PExpr_Bool True

tcExpr (BVSlt w (RegWithVal _ e1) (RegWithVal _ e2))
  | withKnownNat w $ bvSLt e1 e2
  = greturn $ Just $ PExpr_Bool True
tcExpr (BVSlt w (RegWithVal _ e1) (RegWithVal _ e2))
  | withKnownNat w $ not (bvCouldBeSLt e1 e2)
  = greturn $ Just $ PExpr_Bool False
tcExpr (BVSle w (RegWithVal _ e1) (RegWithVal _ e2))
  | withKnownNat w $ bvSLt e2 e1
  = greturn $ Just $ PExpr_Bool False
tcExpr (BVSle w (RegWithVal _ e1) (RegWithVal _ e2))
  | withKnownNat w $ not (bvCouldBeSLt e2 e1)
  = greturn $ Just $ PExpr_Bool True

tcExpr (BVNonzero w (RegWithVal _ bv))
  | bvEq bv (withKnownNat w $ bvInt 0) = greturn $ Just $ PExpr_Bool False
tcExpr (BVNonzero _ (RegWithVal _ bv))
  | not (bvZeroable bv) = greturn $ Just $ PExpr_Bool True

-- String expressions --

tcExpr (StringLit (UnicodeLiteral text)) =
  greturn $ Just $ PExpr_String $ Text.unpack text

-- Struct expressions --

-- For a struct built from registers r1, ..., rn, return struct(r1,...,rn)
tcExpr (MkStruct _ vars) =
  greturn $ Just $ PExpr_Struct $ namesToExprs $
  RL.map (typedRegVar . regWithValReg) $ assignToRList vars

-- For GetStruct x ix, if x has a value it will have been eta-expanded to a
-- struct expression, so simply get out the required field of that struct
tcExpr (GetStruct (RegWithVal r (PExpr_Struct es)) ix _) =
  getVarType (typedRegVar r) >>>= \(StructRepr tps) ->
  let memb = indexToMember (Ctx.size tps) ix in
  greturn $ Just $ RL.get memb (exprsToRAssign es)

-- For SetStruct x ix y, if x has a value it will have been eta-expanded to a
-- struct expression, so simply replace required field of that struct with y
tcExpr (SetStruct tps (RegWithVal _ (PExpr_Struct es)) ix r') =
  let memb = indexToMember (Ctx.size tps) ix in
  greturn $ Just $ PExpr_Struct $ rassignToExprs $
  RL.set memb (PExpr_Var $ typedRegVar $ regWithValReg r') $
  exprsToRAssign es

-- Misc expressions --

tcExpr _ = greturn Nothing


-- | Test if a sequence of arguments could potentially satisfy some function
-- input permissions. This is an overapproximation, meaning that we might return
-- 'True' even if the arguments do not satisfy the permissions.
couldSatisfyPermsM :: PermCheckExtC ext => CruCtx args -> TypedRegs args ->
                      Mb ghosts (ValuePerms args) ->
                      StmtPermCheckM ext cblocks blocks tops ret ps ps Bool
couldSatisfyPermsM CruCtxNil _ _ = greturn True
couldSatisfyPermsM (CruCtxCons tps (BVRepr _)) (TypedRegsCons args arg)
                   (mbMatch -> [nuMP| ValPerms_Cons ps (ValPerm_Eq mb_e) |]) =
  couldSatisfyPermsM tps args ps >>>= \b ->
  getRegEqualsExpr arg >>>= \arg_val ->
  greturn (b && mbLift (fmap (bvCouldEqual arg_val) mb_e))
couldSatisfyPermsM (CruCtxCons tps _) (TypedRegsCons args arg) 
                   (mbMatch -> [nuMP| ValPerms_Cons ps
                                       (ValPerm_Eq (PExpr_LLVMWord mb_e)) |]) =
  couldSatisfyPermsM tps args ps >>>= \b ->
  getRegEqualsExpr arg >>>= \arg_val ->
  case arg_val of
    PExpr_LLVMWord e ->
      greturn (b && mbLift (fmap (bvCouldEqual e) mb_e))
    _ -> greturn False
couldSatisfyPermsM (CruCtxCons tps _) (TypedRegsCons args _)
                   (mbMatch -> [nuMP| ValPerms_Cons ps _ |]) =
  couldSatisfyPermsM tps args ps


-- | Typecheck a statement and emit it in the current statement sequence,
-- starting and ending with an empty stack of distinguished permissions
tcEmitStmt :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
              Stmt ext ctx ctx' ->
              StmtPermCheckM ext cblocks blocks tops ret RNil RNil
              (CtxTrans ctx')
tcEmitStmt ctx loc stmt =
  stmtTraceM (const (pretty "Type-checking statement:" <+>
                     ppStmt (size ctx) stmt)) >>>
  permGetPPInfo >>>= \(!_ppInfo) ->
  mapM (\(Some r) -> ppCruRegAndPerms ctx r) (stmtInputRegs stmt) >>>= \(!pps) ->
  stmtTraceM (const (pretty "Input perms:" <> softline <> ppCommaSep pps)) >>>= \(!_) ->
  tcEmitStmt' ctx loc stmt >>>= \(!ctx') ->
  mapM (\(Some r) -> ppCruRegAndPerms ctx' r) (stmtOutputRegs
                                               (Ctx.size ctx')
                                               stmt) >>>= \(!pps') ->
  stmtTraceM (const (pretty "Output perms:" <> softline <> ppCommaSep pps')) >>>
  greturn ctx'


tcEmitStmt' :: PermCheckExtC ext => CtxTrans ctx -> ProgramLoc ->
               Stmt ext ctx ctx' ->
               StmtPermCheckM ext cblocks blocks tops ret RNil RNil
               (CtxTrans ctx')

tcEmitStmt' ctx loc (SetReg _ (App (ExtensionApp e_ext
                                    :: App ext (Reg ctx) tp)))
  | ExtRepr_LLVM <- knownRepr :: ExtRepr ext
  = tcEmitLLVMSetExpr Proxy ctx loc e_ext

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

tcEmitStmt' ctx loc (CallHandle ret freg_untyped _args_ctx args_untyped) =
  let freg = tcReg ctx freg_untyped
      args = tcRegs ctx args_untyped
      {- args_subst = typedRegsToVarSubst args -} in
  {- getVarTypes (typedRegsToVars args) >>>= \argTypes -> -}
  getSimpleRegPerm freg >>>= \p_freg ->
  (case p_freg of
      ValPerm_Conj ps ->
        forM ps $ \p -> case p of
        Perm_Fun fun_perm ->
          -- FIXME: rewrite couldSatisfyPermsM to fit ghosts having permissions
          {- couldSatisfyPermsM argTypes args (fmap (varSubst args_subst) $
                                            funPermIns fun_perm) >>>= \could -> -}
          let could = True in
          greturn (if could then Just (SomeFunPerm fun_perm) else Nothing)
        _ -> greturn Nothing
      _ -> greturn []) >>>= \maybe_fun_perms ->
  (stmtEmbedImplM $ foldr1WithDefault implCatchM
   (implFailMsgM "Could not find function permission")
   (mapMaybe (fmap greturn) maybe_fun_perms)) >>>= \some_fun_perm ->
  case some_fun_perm of
    SomeFunPerm fun_perm ->
      let ghosts = funPermGhosts fun_perm
          args_ns = typedRegsToVars args in
      (stmtProvePermsFreshLs ghosts (funPermExDistIns
                                     fun_perm args_ns)) >>>= \gsubst ->
      let gexprs = exprsOfSubst gsubst in
      (RL.split ghosts args_ns <$>
       distPermsVars <$> view distPerms <$> stCurPerms <$> gget)
      >>>= \(ghosts_ns,_) ->
      stmtProvePermsAppend CruCtxNil (emptyMb $
                                      eqDistPerms ghosts_ns gexprs) >>>= \_ ->
      stmtProvePerm freg (emptyMb $ ValPerm_Conj1 $ Perm_Fun fun_perm) >>>= \_ ->
      (emitStmt (singletonCruCtx ret) loc
       (TypedCall freg fun_perm (varsToTypedRegs
                                 ghosts_ns) gexprs args)) >>>= \(_ :>: ret') ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret')

tcEmitStmt' ctx loc (Assert reg msg) =
  let treg = tcReg ctx reg in
  getRegEqualsExpr treg >>>= \treg_expr ->
  case treg_expr of
    PExpr_Bool True -> greturn ctx
    PExpr_Bool False -> stmtFailM (\_ -> pretty "Failed assertion")
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
tcEmitLLVMSetExpr _arch ctx loc (LLVM_PointerExpr w blk_reg off_reg) =
  let toff_reg = tcReg ctx off_reg
      tblk_reg = tcReg ctx blk_reg in
  resolveConstant tblk_reg >>>= \maybe_const ->
  case maybe_const of
    Just 0 ->
      withKnownNat w $
      emitLLVMStmt knownRepr loc (ConstructLLVMWord toff_reg) >>>= \x ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx x)
    _ -> stmtFailM (\i -> pretty "LLVM_PointerExpr: Non-zero pointer block: "
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
tcEmitLLVMSetExpr _arch ctx loc (LLVM_PointerBlock w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg in
  withKnownNat w $
  getAtomicOrWordLLVMPerms tptr_reg >>>= \eith ->
  case eith of
    Left e ->
      emitLLVMStmt knownRepr loc (AssertLLVMWord tptr_reg e) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Right _ ->
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
tcEmitLLVMSetExpr _arch ctx loc (LLVM_PointerOffset w ptr_reg) =
  let tptr_reg = tcReg ctx ptr_reg in
  withKnownNat w $
  getAtomicOrWordLLVMPerms tptr_reg >>>= \eith ->
  case eith of
    Left e ->
      emitLLVMStmt knownRepr loc (DestructLLVMWord
                                  tptr_reg e) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Right _ ->
      stmtRecombinePerms >>>
      stmtProvePerm tptr_reg (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr tptr_reg) >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (BVLit w $ BV.mkBV w 0)
                              (Just $ bvInt 0)) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

-- An if-then-else at pointer type is just preserved, though we propogate
-- equality information when possible
tcEmitLLVMSetExpr _arch ctx loc (LLVM_PointerIte w cond_reg then_reg else_reg) =
  withKnownNat w $
  let tcond_reg = tcReg ctx cond_reg
      tthen_reg = tcReg ctx then_reg
      telse_reg = tcReg ctx else_reg in
  getRegEqualsExpr tcond_reg >>>= \tcond_expr ->
  case tcond_expr of
    PExpr_Bool True ->
      emitStmt knownRepr loc (TypedSetRegPermExpr knownRepr $ PExpr_Var $
                              typedRegVar tthen_reg) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    PExpr_Bool False ->
      emitStmt knownRepr loc (TypedSetRegPermExpr knownRepr $ PExpr_Var $
                              typedRegVar telse_reg) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    _ ->
      emitLLVMStmt knownRepr loc (TypedLLVMIte
                                  tcond_reg tthen_reg telse_reg) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

-- For LLVM side conditions, treat each side condition as an assert
tcEmitLLVMSetExpr _arch ctx loc (LLVM_SideConditions tp conds reg) =
  let treg = tcReg ctx reg in
  foldr
  (\(LLVMSideCondition cond_reg ub) rest_m ->
    let tcond_reg = tcReg ctx cond_reg
        err_str = renderDoc (pretty "Undefined behavior: " <> softline <> UB.explain ub) in
    getRegEqualsExpr tcond_reg >>>= \tcond_expr ->
    case tcond_expr of
      PExpr_Bool True ->
        rest_m
      PExpr_Bool False -> stmtFailM (\_ -> pretty err_str)
      _ ->
        emitStmt knownRepr loc (TypedSetRegPermExpr knownRepr $
                                PExpr_String err_str) >>>= \(_ :>: str_var) ->
        stmtRecombinePerms >>>
        emitStmt CruCtxNil loc (TypedAssert tcond_reg $
                                TypedReg str_var) >>>= \_ ->
        stmtRecombinePerms >>>
        rest_m)
  (emitStmt (singletonCruCtx tp) loc (TypedSetRegPermExpr tp $ PExpr_Var $
                                      typedRegVar treg) >>>= \(_ :>: ret) ->
    stmtRecombinePerms >>>
    greturn (addCtxName ctx ret))
  conds


-- FIXME HERE: move withLifetimeCurrentPerms somewhere better...

-- | Perform a statement type-checking conversation inside a context where the
-- supplied lifetime has been proved to be current using the supplied
-- 'LifetimeCurrentPerms'
withLifetimeCurrentPerms ::
  PermCheckExtC ext => PermExpr LifetimeType ->
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
  (1 <= w, KnownNat w, w ~ ArchWidth arch,
   1 <= sz, KnownNat sz, PermCheckExtC (LLVM arch)) =>
  Proxy arch -> ProgramLoc ->
  TypedReg (LLVMPointerType w) -> LLVMFieldPerm w sz -> DistPerms ps ->
  StmtPermCheckM (LLVM arch) cblocks blocks tops ret
  (ps :> LLVMPointerType w :> LLVMPointerType sz)
  (ps :> LLVMPointerType w)
  (Name (LLVMPointerType sz))
emitTypedLLVMLoad _ loc treg fp ps =
  withLifetimeCurrentPerms (llvmFieldLifetime fp) $ \cur_perms ->
  emitLLVMStmt knownRepr loc (TypedLLVMLoad treg fp ps cur_perms)


-- | Emit a 'TypedLLVMStore' instruction, assuming the given LLVM field
-- permission is on the top of the stack. Prove the required lifetime
-- permissions as part of this process, and pop the resulting lifetime
-- permission off the stack before returning. Return the resulting return
-- register of unit type.
emitTypedLLVMStore ::
  (1 <= w, KnownNat w, w ~ ArchWidth arch, 1 <= sz, KnownNat sz) =>
  Proxy arch -> ProgramLoc ->
  TypedReg (LLVMPointerType w) ->
  LLVMFieldPerm w sz ->
  PermExpr (LLVMPointerType sz) -> DistPerms ps ->
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

-- Type-check a word-sized load of an LLVM pointer by requiring a standard ptr
-- permission and using TypedLLVMLoad
tcEmitLLVMStmt arch ctx loc (LLVM_Load _ ptr tp storage _)
  | Just (Some sz) <- someNat $ bytesToBits $ storageTypeSize storage
  , Left leq_proof <- decideLeq (knownNat @1) sz =
    withKnownNat sz $ withLeqProof leq_proof $
    let tptr = tcReg ctx ptr in
    -- Prove [l]ptr((0,rw) |-> eq(y)) for some l, rw, and y
    stmtProvePerm tptr (llvmPtr0EqExPerm sz) >>>= \impl_res ->
    let fp = subst impl_res (llvmPtr0EqEx sz) in
    -- Emit a TypedLLVMLoad instruction
    emitTypedLLVMLoad arch loc tptr fp DistPermsNil >>>= \z ->
    -- Recombine the resulting permissions onto the stack
    stmtRecombinePerms >>>
    -- Convert the return value to the requested type and return it
    (convertRegType knownRepr loc (TypedReg z) knownRepr tp >>>= \ret ->
      greturn (addCtxName ctx $ typedRegVar ret))

-- Type-check a store of an LLVM pointer
tcEmitLLVMStmt arch ctx loc (LLVM_Store _ ptr tp storage _ val)
  | Just (Some sz) <- someNat $ bytesToBits $ storageTypeSize storage
  , Left leq_proof <- decideLeq (knownNat @1) sz =
    withKnownNat sz $ withLeqProof leq_proof $
    let tptr = tcReg ctx ptr
        tval = tcReg ctx val in
    convertRegType knownRepr loc tval tp (LLVMPointerRepr sz) >>>= \tval' ->
    stmtProvePerm tptr (llvmWriteTrueExLPerm sz $ bvInt 0) >>>= \sbst ->
    let l = substLookup sbst Member_Base in
    let fp = llvmFieldWriteTrueL sz (bvInt 0) l in
    emitTypedLLVMStore arch loc tptr fp
    (PExpr_Var $ typedRegVar tval') DistPermsNil >>>= \z ->
    stmtRecombinePerms >>>
    greturn (addCtxName ctx z)

-- Type-check a clear instruction by getting the list of field permissions
-- returned by 'llvmFieldsOfSize' and storing word 0 to each of them
tcEmitLLVMStmt arch ctx loc (LLVM_MemClear _ ptr bytes) =
  let tptr = tcReg ctx ptr
      w = archWidth arch
      flds = llvmFieldsOfSize w (bytesToInteger bytes) in

  -- For each field perm, prove it and write 0 to it
  (forM_ @_ @_ @_ @() flds $ \case
      LLVMArrayField fp ->
        stmtProvePerm tptr (emptyMb $ ValPerm_Conj1 $ Perm_LLVMField fp) >>>
        emitTypedLLVMStore arch loc tptr fp (PExpr_LLVMWord $
                                             bvInt 0) DistPermsNil >>>
        stmtRecombinePerms) >>>

  -- Return a fresh unit variable
  emitStmt knownRepr loc (TypedSetReg knownRepr $
                          TypedExpr EmptyApp
                          (Just PExpr_Unit)) >>>= \(_ :>: z) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx z)

{-
-- Type-check a non-empty mem-clear instruction by writing a 0 to the last word
-- and then recursively clearing all but the last word
-- FIXME: add support for using non-word-size ptr perms with MemClear
tcEmitLLVMStmt arch ctx loc (LLVM_MemClear mem ptr bytes) =
  let tptr = tcReg ctx ptr
      bytes' = bytes - bitsToBytes (intValue (archWidth arch))
      off = bytesToInteger bytes' in
  stmtProvePerm tptr (llvmWriteTrueExLPerm
                      (archWidth arch) (bvInt off)) >>>= \sbst ->
  let l = substLookup sbst Member_Base in
  let fp = llvmFieldWriteTrueL (archWidth arch) (bvInt off) l in
  emitTypedLLVMStore arch loc tptr fp (PExpr_LLVMWord $
                                       bvInt 0) DistPermsNil >>>
  stmtRecombinePerms >>>
  tcEmitLLVMStmt arch ctx loc (LLVM_MemClear mem ptr bytes')
-}

-- Type-check an alloca instruction
tcEmitLLVMStmt _arch ctx loc (LLVM_Alloca _w _ sz_reg _ _) =
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
      stmtFailM (\i -> pretty "LLVM_Alloca: non-constant size for"
                       <+> permPretty i sz_treg)
    (Just fp, p, _) ->
      stmtFailM (\i -> pretty "LLVM_Alloca: expected LLVM frame perm for "
                       <+> permPretty i fp <> pretty ", found perm"
                       <+> permPretty i p)
    (Nothing, _, _) ->
      stmtFailM (const $ pretty "LLVM_Alloca: no frame pointer set")

-- Type-check a push frame instruction
tcEmitLLVMStmt _arch ctx loc (LLVM_PushFrame _ _) =
  emitLLVMStmt knownRepr loc TypedLLVMCreateFrame >>>= \fp ->
  setFramePtr (TypedReg fp) >>>
  stmtRecombinePerms >>>
  emitStmt knownRepr loc (TypedSetReg knownRepr
                          (TypedExpr EmptyApp Nothing)) >>>= \(_ :>: y) ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx y)

-- Type-check a pop frame instruction
tcEmitLLVMStmt _arch ctx loc (LLVM_PopFrame _) =
  getFramePtr >>>= \maybe_fp ->
  maybe (greturn ValPerm_True) getRegPerm maybe_fp >>>= \fp_perm ->
  case (maybe_fp, fp_perm) of
    (Just fp, ValPerm_Conj [Perm_LLVMFrame fperms])
      | Some del_perms <- llvmFrameDeletionPerms fperms ->
        stmtProvePerms knownRepr (distPermsToExDistPerms del_perms) >>>= \_ ->
        stmtProvePerm fp (emptyMb fp_perm) >>>= \_ ->
        emitLLVMStmt knownRepr loc (TypedLLVMDeleteFrame
                                    fp fperms del_perms) >>>= \y ->
        gmodify (\st -> st { stExtState = PermCheckExtState_LLVM Nothing }) >>>
        greturn (addCtxName ctx y)
    _ -> stmtFailM (const $ pretty "LLVM_PopFrame: no frame perms")

-- Type-check a pointer offset instruction by emitting OffsetLLVMValue
tcEmitLLVMStmt _arch ctx loc (LLVM_PtrAddOffset _w _ ptr off) =
  let tptr = tcReg ctx ptr
      toff = tcReg ctx off in
  getRegEqualsExpr toff >>>= \off_expr ->
  emitLLVMStmt knownRepr loc (OffsetLLVMValue tptr off_expr) >>>= \ret ->
  stmtRecombinePerms >>>
  greturn (addCtxName ctx ret)

-- Type-check a LoadHandle instruction by looking for a function pointer perm
tcEmitLLVMStmt _arch ctx loc (LLVM_LoadHandle _ _ ptr args ret) =
  let tptr = tcReg ctx ptr
      x = typedRegVar tptr in
  getAtomicLLVMPerms tptr >>>= \ps ->
  case findIndex (\p -> case p of
                     Perm_LLVMFunPtr _ _ -> True
                     _ -> False) ps of
    Just i
      | Perm_LLVMFunPtr tp p <- ps!!i
      , Just Refl <- testEquality tp (FunctionHandleRepr args ret) ->
        stmtEmbedImplM (implCopyConjM x ps i >>>
                        recombinePerm x (ValPerm_Conj ps)) >>>
        emitLLVMStmt (FunctionHandleRepr args ret) loc
        (TypedLLVMLoadHandle tptr tp p) >>>= \ret' ->
        stmtRecombinePerms >>>
        greturn (addCtxName ctx ret')
    _ -> stmtFailM (const $ pretty "LLVM_PopFrame: no function pointer perms")

-- Type-check a ResolveGlobal instruction by looking up the global symbol
tcEmitLLVMStmt _arch ctx loc (LLVM_ResolveGlobal w _ gsym) =
  (stPermEnv <$> top_get) >>>= \env ->
  case lookupGlobalSymbol env gsym w of
    Just (p, _) ->
      emitLLVMStmt knownRepr loc (TypedLLVMResolveGlobal gsym p) >>>= \ret ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)
    Nothing ->
      stmtFailM (const $ pretty ("LLVM_ResolveGlobal: no perms for global "
                                 ++ globalSymbolName gsym))

{-
tcEmitLLVMStmt _arch ctx loc (LLVM_PtrLe _ r1 r2) =
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
                              TypedExpr (BVUle knownRepr
                                         (RegWithVal (TypedReg n1) e1')
                                         (RegWithVal (TypedReg n1) e2'))
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
                                TypedExpr (BVUle knownRepr
                                         (RegWithVal (TypedReg n1) off1)
                                         (RegWithVal (TypedReg n1) off2))
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
                  sep [pretty "Could not compare LLVM pointer values",
                       permPretty i x1, pretty "and", permPretty i x2])
-}

tcEmitLLVMStmt _arch ctx loc (LLVM_PtrEq _ r1 r2) =
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
    (PExpr_LLVMWord _e, asLLVMOffset -> Just (x', _)) ->
      let r' = TypedReg x' in
      stmtProvePerm r' (emptyMb $ ValPerm_Conj1 Perm_IsLLVMPtr) >>>
      emitLLVMStmt knownRepr loc (AssertLLVMPtr r') >>>
      emitStmt knownRepr loc (TypedSetReg knownRepr $
                              TypedExpr (BoolLit False)
                              Nothing) >>>= \(_ :>: ret) ->
      stmtRecombinePerms >>>
      greturn (addCtxName ctx ret)

    -- Symmetrical version of the above case
    (asLLVMOffset -> Just (x', _), PExpr_LLVMWord _e) ->
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
                  sep [pretty "Could not compare LLVM pointer values",
                       permPretty i x1, pretty "and", permPretty i x2])

tcEmitLLVMStmt _arch _ctx _loc stmt =
  error ("tcEmitLLVMStmt: unimplemented statement - " ++ show (ppApp (\_ -> mempty) stmt))

-- FIXME HERE: need to handle PtrEq, PtrLe, and PtrSubtract


----------------------------------------------------------------------
-- * Permission Checking for Jump Targets and Termination Statements
----------------------------------------------------------------------

-- | Simplify and drop permissions @p@ on variable @x@ so they only depend on
-- the determined variables given in the supplied list
simplify1PermForDetVars :: NuMatchingAny1 r =>
                           NameSet CrucibleType -> Name a -> ValuePerm a ->
                           ImplM vars s r RNil RNil ()

-- If the permissions contain an array permission with undetermined borrows,
-- return those undetermined borrows if possible
--
-- FIXME: we should only return borrows if we can; currently, if there are
-- borrows we can't return, we fail here, and should instead just drop the array
-- permission and keep going. To do this, we have to make a way to try to prove
-- a permission, either by changing the ImplM monad or by adding a notion of
-- local implication proofs where failure is scoped inside a proof
simplify1PermForDetVars det_vars x (ValPerm_Conj ps)
  | Just i <-
      findIndex
      (\case
          Perm_LLVMArray ap ->
            any (\b -> not (nameSetIsSubsetOf
                            (freeVars b) det_vars)) (llvmArrayBorrows ap)
          _ -> False) ps
  , Perm_LLVMArray ap <- ps!!i
  , det_borrows <- filter (\b -> nameSetIsSubsetOf
                                 (freeVars b) det_vars) (llvmArrayBorrows ap)
  , ret_p <- ValPerm_Conj1 $ Perm_LLVMArray $ ap { llvmArrayBorrows =
                                                     det_borrows } =
    mbVarsM ret_p >>>= \mb_ret_p ->
    proveVarImpl x mb_ret_p >>>
    (getTopDistPerm x >>>= recombinePerm x) >>>
    getPerm x >>>= \new_p ->
    simplify1PermForDetVars det_vars x new_p

-- If none of the above cases match but p has only determined free variables,
-- just leave p as is
simplify1PermForDetVars det_vars _ p
  | nameSetIsSubsetOf (freeVars p) det_vars = greturn ()

-- Otherwise, drop p, because it is not determined
simplify1PermForDetVars _det_vars x p =
  implPushM x p >>> implDropM x p


-- | Simplify and drop permissions so they only depend on the determined
-- variables given in the supplied list
simplifyPermsForDetVars :: NuMatchingAny1 r => [SomeName CrucibleType] ->
                           ImplM vars s r RNil RNil ()
simplifyPermsForDetVars det_vars_list =
  let det_vars = NameSet.fromList det_vars_list in
  (permSetVars <$> getPerms) >>>= \vars ->
  mapM_ (\(SomeName x) ->
          getPerm x >>>= simplify1PermForDetVars det_vars x) vars


-- | If @x@ has permission @eq(llvmword e)@ where @e@ is not a needed variable
-- (in the supplied set), replace that perm with an existential permission
-- @x:exists z.eq(llvmword z)@. Similarly, if @x@ has permission @eq(e)@ where
-- @e@ is a literal, replace that permission with just @true@.  Also do this
-- inside pointer permissions, by recursively destructing any pointer
-- permissions @ptr((rw,off) |-> p)@ to the permission @ptr((rw,off) |-> eq(y))@
-- for fresh variable @y@ and generalizing unneeded word equalities for @y@.
generalizeUnneededEqPerms1 ::
  NuMatchingAny1 r => NameSet CrucibleType -> Name a -> ValuePerm a ->
  ImplM vars s r ps ps ()

-- For x:eq(y) for needed variable y, do nothing
generalizeUnneededEqPerms1 needed_vars _ (ValPerm_Eq (PExpr_Var y))
  | NameSet.member y needed_vars = greturn ()
generalizeUnneededEqPerms1 needed_vars _ (ValPerm_Eq e@(PExpr_BV _ _))
  | PExpr_Var y <- normalizeBVExpr e
  , NameSet.member y needed_vars = greturn ()

-- Similarly, for x:eq(llvmword y) for needed variable y, do nothing
generalizeUnneededEqPerms1 needed_vars _ (ValPerm_Eq (PExpr_LLVMWord e))
  | PExpr_Var y <- normalizeBVExpr e
  , NameSet.member y needed_vars = greturn ()
generalizeUnneededEqPerms1 _needed_vars x p@(ValPerm_Eq (PExpr_LLVMWord e)) =
  let mb_eq = nu $ \z -> ValPerm_Eq $ PExpr_LLVMWord $ PExpr_Var z in
  implPushM x p >>>
  introExistsM x e mb_eq >>>
  implPopM x (ValPerm_Exists mb_eq)

-- Similarly, for x:eq(y &+ off) for needed variable y, do nothing
generalizeUnneededEqPerms1 needed_vars _ (ValPerm_Eq (PExpr_LLVMOffset y _))
  | NameSet.member y needed_vars = greturn ()

-- For x:eq(e) where e is a literal, just drop the eq(e) permission
generalizeUnneededEqPerms1 _needed_vars x p@(ValPerm_Eq PExpr_Unit) =
  implPushM x p >>> implDropM x p
generalizeUnneededEqPerms1 _needed_vars x p@(ValPerm_Eq (PExpr_Nat _)) =
  implPushM x p >>> implDropM x p
generalizeUnneededEqPerms1 _needed_vars x p@(ValPerm_Eq (PExpr_Bool _)) =
  implPushM x p >>> implDropM x p

-- If x:p1 * ... * pn, generalize the contents of field permissions in the pis
generalizeUnneededEqPerms1 needed_vars x p@(ValPerm_Conj ps)
  | Just i <- findIndex isLLVMFieldPerm ps
  , Perm_LLVMField fp <- ps!!i
  , y_p <- llvmFieldContents fp
  , ps' <- deleteNth i ps
  , (case y_p of
        ValPerm_Eq (PExpr_Var _) -> False
        _ -> True) =
    implPushM x p >>> implExtractConjM x ps i >>>
    implPopM x (ValPerm_Conj ps') >>>
    implElimLLVMFieldContentsM x fp >>>= \y ->
    let fp' = fp { llvmFieldContents = ValPerm_Eq (PExpr_Var y) } in
    implPushM x (ValPerm_Conj ps') >>>
    implInsertConjM x (Perm_LLVMField fp') ps' i >>>
    implPopM x (ValPerm_Conj (take i ps' ++ Perm_LLVMField fp' : drop i ps')) >>>
    generalizeUnneededEqPerms1 needed_vars y y_p
generalizeUnneededEqPerms1 _ _ _ = greturn ()

-- | Find all permissions of the form @x:eq(llvmword e)@ other than those where
-- @e@ is a needed variable, and replace them with @x:exists z.eq(llvmword z)@
generalizeUnneededEqPerms :: NuMatchingAny1 r => ImplM vars s r ps ps ()
generalizeUnneededEqPerms =
  (permSetAllVarPerms <$> getPerms) >>>= \(Some var_perms) ->
  let needed_vars = neededVars var_perms in
  foldDistPerms (\m x p ->
                  m >>> generalizeUnneededEqPerms1 needed_vars x p)
  (greturn ())
  var_perms


-- | Type-check a Crucible jump target
tcJumpTarget :: PermCheckExtC ext => CtxTrans ctx -> JumpTarget cblocks ctx ->
                StmtPermCheckM ext cblocks blocks tops ret RNil RNil
                (AnnotPermImpl (TypedJumpTarget blocks tops) RNil)
tcJumpTarget ctx (JumpTarget blkID args_tps args) =
  top_get >>>= \top_st ->
  gget >>>= \st ->
  (permCheckExtStateNames <$> stExtState <$> gget) >>>= \(Some ext_ns) ->
  let tops_ns = stTopVars st
      args_t = tcRegs ctx args
      args_ns = typedRegsToVars args_t
      tops_args_ns = RL.append tops_ns args_ns
      tops_args_ext_ns = RL.append tops_args_ns ext_ns
      {-
      (gen_perms_hint, join_point_hint) =
        case stFnHandle top_st of
          SomeHandle h ->
            (lookupBlockGenPermsHint (stPermEnv top_st) h
             (stBlockTypes top_st) blkID
            ,
            lookupBlockJoinPointHint (stPermEnv top_st) h
            (stBlockTypes top_st) blkID) -} in

  tcBlockID blkID >>>= \tpBlkID ->

  -- Step 0: run all of the following steps inside a local ImplM computation,
  -- which we run in order to get out an AnnotPermImpl. This ensures that any
  -- simplifications or other changes to permissions that are performed by this
  -- computation are kept inside this local scope, which in turn is necessary so
  -- that when we type-check a condition branch instruction (Br), the
  -- simplifications of each branch do not affect each other.
  pcmRunImplImplM CruCtxNil mempty $

  -- Step 1: Compute the variables whose values are determined by the
  -- permissions on the top and normal arguments as the starting point for
  -- figuring out our ghost variables. The determined variables are the only
  -- variables that could possibly be inferred by a caller, and they are the
  -- only variables that could actually be accessed by the block we are calling,
  -- so we should not be really giving up any permissions we need.
  let orig_cur_perms = stCurPerms st
      det_vars =
        namesToNamesList tops_args_ext_ns ++
        determinedVars orig_cur_perms tops_args_ext_ns in

  -- Step 2: Simplify and drop permissions so they do not depend on undetermined
  -- variables
  simplifyPermsForDetVars det_vars >>>

  -- Step 3: if gen_perms_hint is set, generalize any permissions of the form
  -- eq(llvmword e) to exists z.eq(llvmword z) as long as they do not determine
  -- a variable that we need, i.e., as long as they are not of the form
  -- eq(llvmword x) for a variable x that we need
  -- (if gen_perms_hint then generalizeUnneededEqPerms else greturn ()) >>>

  -- Step 4: Compute the ghost variables for the target block as those variables
  -- whose values are determined by the permissions on the top and normal
  -- arguments after our above simplifications, adding in the extension-specific
  -- variables as well
  getPerms >>>= \cur_perms ->
  case namesListToNames $ determinedVars cur_perms tops_args_ext_ns of
    SomeRAssign ghosts_ns' ->
      localImplM $
      let ghosts_ns = RL.append ext_ns ghosts_ns'
          tops_perms = varPermsMulti tops_ns cur_perms
          tops_set = NameSet.fromList $ namesToNamesList tops_ns
          ghosts_perms = varPermsMulti ghosts_ns cur_perms
          args_perms =
            buildDistPerms (\n -> if NameSet.member n tops_set then
                                    ValPerm_Eq (PExpr_Var n)
                                  else cur_perms ^. varPerm n) args_ns
          perms_in = appendDistPerms (appendDistPerms
                                      tops_perms args_perms) ghosts_perms in
      implTraceM (\i ->
                   pretty ("tcJumpTarget " ++ show blkID ++ " (unvisited)") <>
                   {- (if gen_perms_hint then pretty "(gen)" else emptyDoc) <> -}
                   line <>
                   (case permSetAllVarPerms orig_cur_perms of
                       Some all_perms ->
                         pretty "Current perms:" <+>
                         align (permPretty i all_perms))
                   <> line <>
                   pretty "Determined vars:"<+>
                   align (list (map (permPretty i) det_vars)) <> line <>
                   pretty "Input perms:" <+>
                   hang 2 (permPretty i perms_in)) >>>

      -- Step 5: abstract all the variables out of the input permissions.  Note
      -- that abstractVars uses the left-most occurrence of any variable that
      -- occurs multiple times in the variable list and we want our eq perms for
      -- our args to map to our tops, not our args, so this order works for what
      -- we want
      (case abstractVars
            (RL.append (RL.append tops_ns args_ns) ghosts_ns)
            (distPermsToValuePerms perms_in) of
          Just ps -> greturn ps
          Nothing
            | SomeRAssign orig_det_vars <- namesListToNames det_vars
            , orig_perms <- varPermsMulti orig_det_vars orig_cur_perms ->
              implTraceM
              (\i ->
                pretty ("tcJumpTarget: unexpected free variable in perms_in:\n"
                        ++ renderDoc (permPretty i perms_in)
                        ++ "\norig_perms:\n"
                        ++ renderDoc (permPretty i orig_perms))) >>>= \str ->
              error str) >>>= \cl_mb_perms_in ->

      -- Step 6: insert a new block entrypoint that has all the permissions
      -- we constructed above as input permissions
      implGetVarTypes ghosts_ns >>>= \ghosts_tps ->
      (case stCurEntry st of
          Some curEntryID ->
            liftGenStateContM $ flip runReaderT top_st $
            callBlockWithPerms curEntryID tpBlkID
            ghosts_tps cl_mb_perms_in) >>>= \siteID ->

      -- Step 7: return a TypedJumpTarget inside a PermImpl that proves all the
      -- required input permissions from the current permission set by copying
      -- the existing permissions into the current distinguished perms, except
      -- for the eq permissions for real arguments, which are proved by
      -- reflexivity.
      implWithoutTracingM (implPushOrReflMultiM perms_in) >>>
      greturn (PermImpl_Done $
               TypedJumpTarget siteID Proxy (mkCruCtx args_tps) perms_in)


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
    PExpr_Bool True -> trace "tcTermStmt: br reg known to be true!" $
                       TypedJump <$> tcJumpTarget ctx tgt1
    PExpr_Bool False -> trace "tcTermStmt: br reg known to be false!" $
                        TypedJump <$> tcJumpTarget ctx tgt2
    _ -> trace "tcTermStmt: br reg unknown, checking both branches..." $
         TypedBr treg <$> tcJumpTarget ctx tgt1 <*> tcJumpTarget ctx tgt2
tcTermStmt ctx (Return reg) =
  let treg = tcReg ctx reg in
  gget >>>= \st ->
  top_get >>>= \top_st ->
  let tops = stTopVars st
      mb_ret_perms =
        varSubst (permVarSubstOfNames tops) $
        mbSeparate (MNil :>: Proxy) $
        mbValuePermsToDistPerms (stRetPerms top_st)
      req_perms =
        varSubst (singletonVarSubst $ typedRegVar treg) mb_ret_perms
      err = pretty "Could not prove:" <+> permPretty (stPPInfo st) req_perms in
  TypedReturn <$>
  pcmRunImplM CruCtxNil err
  (const $ TypedRet Refl (stRetType top_st) treg mb_ret_perms)
  (proveVarsImpl $ distPermsToExDistPerms req_perms)
tcTermStmt ctx (ErrorStmt reg) =
  let treg = tcReg ctx reg in
  getRegPerm treg >>>= \treg_p ->
  let maybe_str = case treg_p of
        ValPerm_Eq (PExpr_String str) -> Just str
        _ -> Nothing in
  greturn $ TypedErrorStmt maybe_str treg
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
  setErrorPrefix loc (ppStmt (Ctx.size ctx) stmt) ctx (stmtInputRegs stmt) >>>
  tcEmitStmt ctx loc stmt >>>= \ctx' -> tcEmitStmtSeq ctx' stmts
tcEmitStmtSeq ctx (TermStmt loc tstmt) =
  setErrorPrefix loc (pretty tstmt) ctx (termStmtRegs tstmt) >>>
  tcTermStmt ctx tstmt >>>= \typed_tstmt ->
  gmapRet (>> return (TypedTermStmt loc typed_tstmt))

-- | Type-check the body of a Crucible block as the body of an entrypoint
tcBlockEntryBody ::
  PermCheckExtC ext => Block ext cblocks ret args ->
  TypedEntry TCPhase ext blocks tops ret (CtxToRList args) ghosts ->
  TopPermCheckM ext cblocks blocks tops ret
  (Mb ((tops :++: CtxToRList args) :++: ghosts)
   (TypedStmtSeq ext blocks tops ret ((tops :++: CtxToRList args) :++: ghosts)))
tcBlockEntryBody blk (TypedEntry {..}) =
  get >>= \(TopPermCheckState {..}) ->
  runPermCheckM typedEntryID typedEntryArgs typedEntryGhosts typedEntryPermsIn $
  \tops_ns args_ns ghosts_ns perms ->
  let ctx = mkCtxTrans (blockInputs blk) args_ns
      ns = RL.append (RL.append tops_ns args_ns) ghosts_ns in
  stmtTraceM (\i ->
               pretty "Type-checking block" <+> pretty (blockID blk) <>
               comma <+> pretty "entrypoint" <+> pretty (entryIndex typedEntryID)
               <> line <>
               pretty "Input types:"
               <> align (permPretty i $
                         RL.map2 VarAndType ns $ cruCtxToTypes $
                         appendCruCtx (appendCruCtx stTopCtx typedEntryArgs)
                         typedEntryGhosts)
               <> line <>
               pretty "Input perms:"
               <> align (permPretty i perms)) >>>
  stmtRecombinePerms >>>
  tcEmitStmtSeq ctx (blk ^. blockStmts)


-- | Prove that the permissions held at a call site from the given source
-- entrypoint imply the supplied input permissions of the current entrypoint
proveCallSiteImpl ::
  KnownRepr ExtRepr ext => TypedEntryID blocks some_args ->
  TypedEntryID blocks args -> CruCtx args -> CruCtx ghosts -> CruCtx vars ->
  MbValuePerms ((tops :++: args) :++: vars) ->
  MbValuePerms ((tops :++: args) :++: ghosts) ->
  TopPermCheckM ext cblocks blocks tops ret (CallSiteImpl
                                             blocks
                                             ((tops :++: args) :++: vars)
                                             tops args ghosts)
proveCallSiteImpl srcID destID args ghosts vars mb_perms_in mb_perms_out =
  fmap CallSiteImpl $ runPermCheckM srcID args vars mb_perms_in $
  \tops_ns args_ns _ perms_in ->
  let perms_out =
        varSubst (permVarSubstOfNames $ RL.append tops_ns args_ns) $
        mbSeparate (cruCtxProxies ghosts) $
        mbValuePermsToDistPerms mb_perms_out in
  permGetPPInfo >>>= \ppInfo ->
  let err = pretty "Could not prove" <+> permPretty ppInfo perms_out in
  pcmRunImplM ghosts err (CallSiteImplRet destID ghosts Refl .
                          exprsOfSubst . completePSubst ghosts)
  (recombinePerms perms_in >>>
   proveVarsImpl perms_out >>> getPSubst) >>>= \impl ->
  gmapRet (>> return impl)

-- | Visit a call site, proving its implication of the entrypoint input
-- permissions if that implication does not already exist
visitCallSite :: PermCheckExtC ext =>
                 TypedEntry TCPhase ext blocks tops ret args ghosts ->
                 TypedCallSite TCPhase blocks tops args ghosts vars ->
                 TopPermCheckM ext cblocks blocks tops ret
                 (TypedCallSite TCPhase blocks tops args ghosts vars)
visitCallSite _ site@(TypedCallSite { typedCallSiteImpl = Just _ }) =
  return site
visitCallSite (TypedEntry {..}) site@(TypedCallSite {..})
  | TypedCallSiteID { callSiteSrc = srcID,
                      callSiteVars = vars } <- typedCallSiteID =
    fmap (\impl -> site { typedCallSiteImpl = Just impl }) $
    proveCallSiteImpl srcID typedEntryID
    typedEntryArgs typedEntryGhosts vars
    typedCallSitePerms typedEntryPermsIn

-- | Visit an entrypoint, by first proving the required implications at each
-- call site, meaning that the permissions held at the call site imply the input
-- permissions of the entrypoint, and then type-checking the body of the block
-- with those input permissions, if it has not been type-checked already
--
-- FIXME HERE: if some of the call site implications fail, recompute the
-- entrypoint input permissions using widening
visitEntry :: (PermCheckExtC ext, CtxToRList cargs ~ args) =>
              Block ext cblocks ret cargs ->
              TypedEntry TCPhase ext blocks tops ret args ghosts ->
              TopPermCheckM ext cblocks blocks tops ret
              (TypedEntry TCPhase ext blocks tops ret args ghosts)
visitEntry blk entry@(TypedEntry {..}) =
  do callers <- mapM (traverseF $ visitCallSite entry) typedEntryCallers
     body <- maybe (tcBlockEntryBody blk entry) return typedEntryBody
     return $ entry { typedEntryCallers = callers, typedEntryBody = Just body }

-- | Visit a block by visiting all its entrypoints
visitBlock :: PermCheckExtC ext =>
              TypedBlock TCPhase ext blocks tops ret args ->
              TopPermCheckM ext cblocks blocks tops ret
              (TypedBlock TCPhase ext blocks tops ret args)
visitBlock blk@(TypedBlock {..}) =
  (stCBlocksEq <$> get) >>= \Refl ->
  flip (set typedBlockEntries) blk <$>
  mapM (traverseF $ visitEntry typedBlockBlock) _typedBlockEntries

-- | Flatten a list of topological ordering components to a list of nodes in
-- topological order paired with a flag denoting which nodes were loop heads
wtoCompsToListWithSCCs :: [WTOComponent n] -> [(n,Bool)]
wtoCompsToListWithSCCs =
  concatMap (\case
                Vertex n -> [(n,False)]
                SCC n comps -> [(n,True)] ++ wtoCompsToListWithSCCs comps)

-- | Build a topologically sorted list of 'BlockID's for a 'CFG', along with a
-- flag for each 'BlockID' indicating whether it is the head of a loop
cfgOrderWithSCCs :: CFG ext blocks init ret ->
                    ([Some (BlockID blocks)], Assignment (Constant Bool) blocks)
cfgOrderWithSCCs cfg =
  let nodes_sccs = wtoCompsToListWithSCCs $ cfgWeakTopologicalOrdering cfg in
  (map fst nodes_sccs,
   foldr (\(Some blkID, is_scc) ->
           set (ixF $ blockIDIndex blkID) $ Constant is_scc)
   (fmapFC (const $ Constant False) $ cfgBlockMap cfg)
   nodes_sccs)

-- | Type-check a Crucible CFG
tcCFG :: forall ext cblocks ghosts inits ret. PermCheckExtC ext =>
         PermEnv -> EndianForm ->
         FunPerm ghosts (CtxToRList inits) ret ->
         CFG ext cblocks inits ret ->
         TypedCFG ext (CtxCtxToRList cblocks) ghosts (CtxToRList inits) ret
tcCFG env endianness fun_perm cfg =
  let h = cfgHandle cfg
      ghosts = funPermGhosts fun_perm
      (nodes, sccs) = cfgOrderWithSCCs cfg
      init_st = emptyTopPermCheckState env fun_perm endianness cfg sccs
      tp_nodes = map (\(Some blkID) ->
                       Some $ stLookupBlockID blkID init_st) nodes in
  let tp_blk_map = flip evalState init_st $ main_loop tp_nodes in
  TypedCFG { tpcfgHandle = TypedFnHandle ghosts h
           , tpcfgFunPerm = fun_perm
           , tpcfgBlockMap = tp_blk_map
           , tpcfgEntryID =
               TypedEntryID (stLookupBlockID (cfgEntryBlockID cfg) init_st) 0 }
  where
    main_loop :: [Some (TypedBlockID blocks)] ->
                 TopPermCheckM ext cblocks blocks tops ret
                 (TypedBlockMap TransPhase ext blocks tops ret)
    main_loop nodes =
      get >>= \st ->
      case completeTypedBlockMap $ view stBlockMap st of
        Just blkMapOut -> return blkMapOut
        Nothing ->
          forM_ nodes (\(Some tpBlkID) ->
                        use (stBlockMap . member tpBlkID) >>=
                        (visitBlock >=>
                         assign (stBlockMap . member tpBlkID))) >>
          main_loop nodes
