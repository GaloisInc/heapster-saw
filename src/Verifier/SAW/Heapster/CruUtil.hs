{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Heapster.CruUtil where

import Data.Kind
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Reflection
import Data.List.NonEmpty (NonEmpty(..))
import Data.ByteString
import Numeric
import Numeric.Natural
import qualified Data.BitVector.Sized as BV
import System.FilePath

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NuMatching

import What4.ProgramLoc
import What4.Partial
import What4.InterpretedFloatingPoint (X86_80Val(..))
import What4.Interface (RoundingMode(..),StringLiteral(..), stringLiteralInfo)
import What4.Utils.Word16String (Word16String (..))

import Data.Parameterized.Context hiding ((:>), empty, take, view)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import Data.Parameterized.BoolRepr

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Text.LLVM.AST as L
import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core hiding (App)
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.Extension.Safety
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.Extension.Safety.Poison as Poison
import qualified Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior as UB
import Verifier.SAW.Term.Functor
import Verifier.SAW.OpenTerm

----------------------------------------------------------------------
-- * Building 'NuMatching' and 'Closable' Instances for Crucible Types
----------------------------------------------------------------------

-- | A reification of an object of type @a@ at type level
data ReifiesObj a = forall s. Reifies s a => ReifiesObj (Proxy s)

$(mkNuMatching [t| forall a. ReifiesObj a |])

-- | Build a 'ReifiesObj' containing a value
mkReifiesObj :: a -> ReifiesObj a
mkReifiesObj a = reify a ReifiesObj

-- | Project out the value contained in a 'ReifiesObj'
projReifiesObj :: ReifiesObj a -> a
projReifiesObj (ReifiesObj prx) = reflect prx

instance NuMatching Ident where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable Ident where
  toClosed = unsafeClose

instance Liftable Ident where
  mbLift = unClosed . mbLift . fmap toClosed

-- FIXME: this Natural instance should go into Hobbits
instance Closable Natural where
  toClosed = unsafeClose

-- FIXME: move to Hobbits
class NuMatchingAny1 f => LiftableAny1 f where
  mbLiftAny1 :: Mb ctx (f a) -> f a

-- FIXME: move to Hobbits
instance NuMatchingAny1 Proxy where
  nuMatchingAny1Proof = nuMatchingProof

-- FIXME: move to Hobbits
instance LiftableAny1 Proxy where
  mbLiftAny1 = mbLift

-- FIXME: move to Hobbits
instance LiftableAny1 f => Liftable (RAssign f ctx) where
  mbLift [nuP| MNil |] = MNil
  mbLift [nuP| xs :>: x |] = mbLift xs :>: mbLiftAny1 x

instance NuMatching OpenTerm where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching GlobalSymbol where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable GlobalSymbol where
  toClosed = unsafeClose

instance Liftable GlobalSymbol where
  mbLift = unClosed . mbLift . fmap toClosed

-- | This is copied from 'Lang.Crucible.LLVM.Types', as that module is hidden
globalSymbolName :: GlobalSymbol -> String
globalSymbolName (GlobalSymbol (L.Symbol str)) = str

instance NuMatching (SymbolRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (BoolRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (BoolRepr tp) where
  toClosed = unsafeClose

instance Liftable (BoolRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching (NatRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (NatRepr tp) where
  toClosed = unsafeClose

instance Liftable (NatRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching (TypeRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (TypeRepr tp) where
  toClosed = unsafeClose

instance Liftable (TypeRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching (BaseTypeRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (BaseTypeRepr tp) where
  toClosed = unsafeClose

instance Liftable (BaseTypeRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

-- NOTE: this is handled by the Assignment instance
-- instance NuMatching (CtxRepr ctx) where
--   nuMatchingProof = isoMbTypeRepr mkKnownReprObj getKnownReprObj

instance NuMatching (Index ctx a) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching Text where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable Text where
  toClosed = unsafeClose

instance Liftable Text where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching ProgramLoc where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable ProgramLoc where
  toClosed = unsafeClose

instance Liftable ProgramLoc where
  mbLift = unClosed . mbLift . fmap toClosed

-- | Pretty-print a 'Position' with a "short" filename, without the path
ppShortFileName :: Position -> PP.Doc
ppShortFileName (SourcePos path l c) =
  PP.text (takeFileName $ Text.unpack path)
    PP.<> PP.colon PP.<> PP.int l
    PP.<> PP.colon PP.<> PP.int c
ppShortFileName (BinaryPos path addr) =
  PP.text (takeFileName $ Text.unpack path) PP.<> PP.colon PP.<>
    PP.text "0x" PP.<> PP.text (showHex addr "")
ppShortFileName (OtherPos txt) = PP.text (Text.unpack txt)
ppShortFileName InternalPos = PP.text "internal"

instance NuMatching ByteString where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching MemoryLoadError where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (FnHandle args ret) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching SomeHandle where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (FloatInfoRepr fi) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching RoundingMode where
  nuMatchingProof = unsafeMbTypeRepr

$(mkNuMatching [t| forall f. NuMatchingAny1 f => Some f |])

instance NuMatchingAny1 BaseTypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 TypeRepr where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall f ctx . NuMatchingAny1 f => AssignView f ctx |])

viewToAssign :: AssignView f ctx -> Assignment f ctx
viewToAssign AssignEmpty = Ctx.empty
viewToAssign (AssignExtend asgn' f) = extend asgn' f

instance NuMatchingAny1 f => NuMatching (Assignment f ctx) where
  nuMatchingProof =
    -- FIXME: inefficient to map a whole Assignment step by step to ViewAssigns,
    -- freshen each element, and then map back to the Assignment again; maybe we
    -- need to figure out how to use the TraversableFC instance for Assignment
    -- here?
    isoMbTypeRepr viewAssign viewToAssign

instance NuMatchingAny1 f => NuMatchingAny1 (Assignment f) where
  nuMatchingAny1Proof = nuMatchingProof

instance Closable (Assignment TypeRepr ctx) where
  toClosed = unsafeClose

instance Liftable (Assignment TypeRepr ctx) where
  mbLift = unClosed . mbLift . fmap toClosed


$(mkNuMatching [t| forall f tp. NuMatchingAny1 f => BaseTerm f tp |])

instance NuMatchingAny1 f => NuMatchingAny1 (BaseTerm f) where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall a. NuMatching a => NonEmpty a |])
$(mkNuMatching [t| forall p v. (NuMatching p, NuMatching v) => Partial p v |])
$(mkNuMatching [t| X86_80Val |])
-- $(mkNuMatching [t| MemoryLoadError |]) -- NOTE: contains unexported types
$(mkNuMatching [t| forall w. BV.BV w |])
$(mkNuMatching [t| Word16String |])
$(mkNuMatching [t| forall s. StringLiteral s |])
$(mkNuMatching [t| forall s. StringInfoRepr s |])
$(mkNuMatching [t| forall ext f tp.
                (NuMatchingAny1 f, NuMatchingAny1 (ExprExtension ext f)) =>
                App ext f tp |])


$(mkNuMatching [t| Bytes |])
$(mkNuMatching [t| forall v. NuMatching v => Field v |])
$(mkNuMatching [t| Alignment |])
$(mkNuMatching [t| UB.PtrComparisonOperator |])
$(mkNuMatching [t| forall v. NuMatching v => StorageTypeF v |])
$(mkNuMatching [t| StorageType |])

$(mkNuMatching [t| forall f. NuMatchingAny1 f => UB.UndefinedBehavior f |])
$(mkNuMatching [t| forall f. NuMatchingAny1 f => Poison.Poison f |])
$(mkNuMatching [t| forall f. NuMatchingAny1 f => BadBehavior f |])
$(mkNuMatching [t| forall f. NuMatchingAny1 f => LLVMSafetyAssertion f |])
$(mkNuMatching [t| forall f. NuMatchingAny1 f => LLVMSideCondition f |])

$(mkNuMatching [t| forall blocks tp. BlockID blocks tp |])

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

instance Closable (BV.BV w) where
  toClosed = unsafeClose

instance Liftable (BV.BV w) where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable Bytes where
  toClosed (Bytes i) =
    $(mkClosed [| Bytes |]) `clApply` (toClosed i)

instance Liftable Bytes where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable (StringLiteral si) where
  toClosed = unsafeClose

instance Liftable (StringLiteral si) where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable (BadBehavior e) where
  toClosed = unsafeClose

instance NuMatchingAny1 e => Liftable (BadBehavior e) where
  mbLift = unClosed . mbLift . fmap toClosed

-- NOTE: Crucible objects can never contain any Hobbits names, but "proving"
-- that would require introspection of opaque types like 'Index' and 'Nonce',
-- and would also be inefficient, so we just use 'unsafeClose'

instance Closable (Block ext cblocks ret args) where
  toClosed = unsafeClose

instance Closable (FnHandle args ret) where
  toClosed = unsafeClose

instance Liftable (FnHandle args ret) where
  mbLift fh = unClosed $ mbLift $ fmap toClosed fh

instance Closable SomeHandle where
  toClosed = unsafeClose

instance Liftable SomeHandle where
  mbLift fh = unClosed $ mbLift $ fmap toClosed fh

-- | Close an assignment whose elements are all 'Closable'
closeAssign :: (forall a. f a -> Closed (f a)) -> Assignment f ctx ->
               Closed (Assignment f ctx)
closeAssign _ (viewAssign -> AssignEmpty) = $(mkClosed [| Ctx.empty |])
closeAssign f (viewAssign -> AssignExtend asgn fa) =
  $(mkClosed [| Ctx.extend |]) `clApply` closeAssign f asgn `clApply` f fa


----------------------------------------------------------------------
-- * Contexts of Crucible Types
----------------------------------------------------------------------

-- | Convert a Crucible 'Ctx' to a Hobbits 'RList'
type family CtxToRList (ctx :: Ctx k) :: RList k where
  CtxToRList EmptyCtx = RNil
  CtxToRList (ctx' ::> x) = CtxToRList ctx' :> x

-- | Convert a Hobbits 'RList' to a Crucible 'Ctx'
type family RListToCtx (ctx :: RList k) :: Ctx k where
  RListToCtx RNil = EmptyCtx
  RListToCtx (ctx' :> x) = RListToCtx ctx' ::> x

-- | Convert a Crucible context of contexts to a Hobbits one
type family CtxCtxToRList (ctx :: Ctx (Ctx k)) :: RList (RList k) where
  CtxCtxToRList EmptyCtx = RNil
  CtxCtxToRList (ctx' ::> c) = CtxCtxToRList ctx' :> CtxToRList c

-- | Convert a Hobbits context of contexts to a Crucible one
type family RListToCtxCtx (ctx :: RList (RList k)) :: Ctx (Ctx k) where
  RListToCtxCtx RNil = EmptyCtx
  RListToCtxCtx (ctx' :> c) = RListToCtxCtx ctx' ::> RListToCtx c

-- | Convert a Crucible 'Assignment' to a Hobbits 'RAssign'
assignToRList :: Assignment f ctx -> RAssign f (CtxToRList ctx)
assignToRList asgn = case viewAssign asgn of
  AssignEmpty -> MNil
  AssignExtend asgn' f -> assignToRList asgn' :>: f

-- | Convert a Hobbits 'RAssign' to a Crucible 'Assignment'
rlistToAssign :: RAssign f ctx -> Assignment f (RListToCtx ctx)
rlistToAssign MNil = Ctx.empty
rlistToAssign (rlist :>: f) = extend (rlistToAssign rlist) f

-- | A data-level encapsulation of the 'KnownRepr' typeclass
data KnownReprObj f a = KnownRepr f a => KnownReprObj

-- | Build a 'KnownReprObj' using a phantom type
mkKnownReprObj :: KnownRepr f a => prx a -> KnownReprObj f a
mkKnownReprObj _ = KnownReprObj

-- | Extract the representation in a 'KnownReprObj'
unKnownReprObj :: KnownReprObj f a -> f a
unKnownReprObj (KnownReprObj :: KnownReprObj f a) = knownRepr :: f a


-- | A context of Crucible types. NOTE: we do not use 'RAssign' here, because
-- we do not yet have a nice way to define the 'NuMatching' instance we want...
data CruCtx ctx where
  CruCtxNil :: CruCtx RNil
  CruCtxCons :: CruCtx ctx -> TypeRepr a -> CruCtx (ctx :> a)

-- $(mkNuMatching [t| forall a. CruType a |])
$(mkNuMatching [t| forall ctx. CruCtx ctx |])

instance Liftable (CruCtx ctx) where
  mbLift [nuP| CruCtxNil |] = CruCtxNil
  mbLift [nuP| CruCtxCons ctx a |] = CruCtxCons (mbLift ctx) (mbLift a)

instance Closable (CruCtx ctx) where
  toClosed CruCtxNil = $(mkClosed [| CruCtxNil |])
  toClosed (CruCtxCons ctx a) =
    $(mkClosed [| CruCtxCons |]) `clApply` toClosed ctx `clApply` toClosed a

instance TestEquality CruCtx where
  testEquality CruCtxNil CruCtxNil = Just Refl
  testEquality (CruCtxCons ctx1 tp1) (CruCtxCons ctx2 tp2)
    | Just Refl <- testEquality ctx1 ctx2
    , Just Refl <- testEquality tp1 tp2
    = Just Refl
  testEquality _ _ = Nothing

instance PP.Pretty (CruCtx ctx) where
  pretty ctx = PP.list $ helper ctx where
    helper :: CruCtx ctx' -> [PP.Doc]
    helper CruCtxNil = []
    helper (CruCtxCons ctx tp) = helper ctx ++ [PP.pretty tp]

instance KnownRepr CruCtx RNil where
  knownRepr = CruCtxNil

instance (KnownRepr CruCtx tps, KnownRepr TypeRepr tp) =>
         KnownRepr CruCtx (tps :> tp) where
  knownRepr = CruCtxCons knownRepr knownRepr

-- | Build a 'CruCtx' from a 'CtxRepr'
mkCruCtx :: CtxRepr ctx -> CruCtx (CtxToRList ctx)
mkCruCtx ctx = case viewAssign ctx of
  AssignEmpty -> CruCtxNil
  AssignExtend ctx' tp -> CruCtxCons (mkCruCtx ctx') tp

-- | Convert a 'CruCtx' to a 'CtxRepr'
cruCtxToRepr :: CruCtx ctx -> CtxRepr (RListToCtx ctx)
cruCtxToRepr CruCtxNil = Ctx.empty
cruCtxToRepr (CruCtxCons ctx tp) = Ctx.extend (cruCtxToRepr ctx) tp

-- | Build a proof that calling 'cruCtxToRepr' followed by 'mkCruCtx' yields
-- equal types
cruCtxToReprEq :: CruCtx ctx -> CtxToRList (RListToCtx ctx) :~: ctx
cruCtxToReprEq CruCtxNil = Refl
cruCtxToReprEq (CruCtxCons ctx tp) =
  case cruCtxToReprEq ctx of
    Refl -> Refl

-- | Convert a 'CruCtx' to an assignment of 'TypeRepr's
--
-- FIXME: 'CruCtx' should just be defined as an assignment!
cruCtxToTypes :: CruCtx ctx -> RAssign TypeRepr ctx
cruCtxToTypes CruCtxNil = MNil
cruCtxToTypes (CruCtxCons tps tp) = cruCtxToTypes tps :>: tp

instance Show (CruCtx ctx) where
  show = show . cruCtxToRepr

-- | The empty context
emptyCruCtx :: CruCtx RNil
emptyCruCtx = CruCtxNil

-- | Build a singleton crucible context
singletonCruCtx :: TypeRepr tp -> CruCtx (RNil :> tp)
singletonCruCtx tp = CruCtxCons CruCtxNil tp

-- | Add an element to the end of a context
extCruCtx :: KnownRepr TypeRepr a => CruCtx ctx -> CruCtx (ctx :> a)
extCruCtx ctx = CruCtxCons ctx knownRepr

-- | Remove an element from the end of a context
unextCruCtx :: CruCtx (ctx :> a) -> CruCtx ctx
unextCruCtx (CruCtxCons ctx _) = ctx

-- | Append two contexts
appendCruCtx :: CruCtx ctx1 -> CruCtx ctx2 -> CruCtx (ctx1 :++: ctx2)
appendCruCtx ctx1 CruCtxNil = ctx1
appendCruCtx ctx1 (CruCtxCons ctx2 tp) = CruCtxCons (appendCruCtx ctx1 ctx2) tp

-- | Build a 'RAssign' phantom argument from a context of Crucible types
cruCtxProxies :: CruCtx ctx -> RAssign Proxy ctx
cruCtxProxies CruCtxNil = MNil
cruCtxProxies (CruCtxCons ctx _) = cruCtxProxies ctx :>: Proxy

-- | Compute the length of a 'CruCtx'
cruCtxLen :: CruCtx ctx -> Int
cruCtxLen CruCtxNil = 0
cruCtxLen (CruCtxCons ctx _) = 1 + cruCtxLen ctx

-- | Look up a type in a 'CruCtx'
cruCtxLookup :: CruCtx ctx -> Member ctx a -> TypeRepr a
cruCtxLookup (CruCtxCons _ tp) Member_Base = tp
cruCtxLookup (CruCtxCons ctx _) (Member_Step memb) = cruCtxLookup ctx memb

-- | Build a 'CruCtx' of the given length.
cruCtxReplicate :: NatRepr n -> TypeRepr a -> Some CruCtx 
cruCtxReplicate n tp =
  case isZeroNat n of
    ZeroNat -> Some CruCtxNil
    NonZeroNat
      | Some ctx <- cruCtxReplicate (predNat n) tp
      -> Some (CruCtxCons ctx tp)


----------------------------------------------------------------------
-- * Misc Operations on Crucible Objects
----------------------------------------------------------------------

-- | Get all the registers used in a Crucible statement
stmtInputRegs :: TraverseExt ext => Stmt ext ctx ctx' -> [Some (Reg ctx)]
stmtInputRegs (SetReg _ (Core.App app)) = foldMapFC (\r -> [Some r]) app
stmtInputRegs (ExtendAssign s') = foldMapFC (\r -> [Some r]) s'
stmtInputRegs (CallHandle _ h _ args) =
  Some h : foldMapFC (\r -> [Some r]) args
stmtInputRegs (Print msg) = [Some msg]
stmtInputRegs (ReadGlobal _) = []
stmtInputRegs (WriteGlobal _ r) = [Some r]
stmtInputRegs (FreshConstant _ _) = []
stmtInputRegs (NewRefCell _ r) = [Some r]
stmtInputRegs (NewEmptyRefCell _) = []
stmtInputRegs (ReadRefCell r) = [Some r]
stmtInputRegs (WriteRefCell r1 r2) = [Some r1, Some r2]
stmtInputRegs (DropRefCell r) = [Some r]
stmtInputRegs (Assert r1 r2) = [Some r1, Some r2]
stmtInputRegs (Assume r1 r2) = [Some r1, Some r2]

-- | Get all the input and output registers of a Crucible statement
stmtOutputRegs :: TraverseExt ext => Size ctx' -> Stmt ext ctx ctx' ->
                  [Some (Reg ctx')]
stmtOutputRegs sz (SetReg _ (Core.App app)) =
  foldMapFC (\r -> [Some $ extendReg r]) app ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs sz (ExtendAssign s') =
  foldMapFC (\r -> [Some $ extendReg r]) s' ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs sz (CallHandle _ h _ args) =
  Some (extendReg h) : foldMapFC (\r -> [Some $ extendReg r]) args
  ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs sz (Print msg) = [Some msg]
stmtOutputRegs sz (ReadGlobal _) = []
stmtOutputRegs sz (WriteGlobal _ r) = [Some r]
stmtOutputRegs sz (FreshConstant _ _) = []
stmtOutputRegs sz (NewRefCell _ r) =
  [Some $ extendReg r] ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs sz (NewEmptyRefCell _) = []
stmtOutputRegs sz (ReadRefCell r) =
  [Some $ extendReg r] ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs sz (WriteRefCell r1 r2) = [Some r1, Some r2]
stmtOutputRegs sz (DropRefCell r) = [Some r]
stmtOutputRegs sz (Assert r1 r2) = [Some r1, Some r2]
stmtOutputRegs sz (Assume r1 r2) = [Some r1, Some r2]

-- | Get all the registers used in a Crucible 'JumpTarget'
jumpTargetRegs :: JumpTarget blocks ctx -> [Some (Reg ctx)]
jumpTargetRegs (JumpTarget _ _ regs) = foldMapFC (\r -> [Some r]) regs

-- | Get all the registers used in a Crucible 'SwitchTarget'
switchTargetRegs :: SwitchTarget blocks ctx tp -> [Some (Reg ctx)]
switchTargetRegs (SwitchTarget _ _ regs) = foldMapFC (\r -> [Some r]) regs

-- | Get all the registers used in a Crucible termination statement
termStmtRegs :: TermStmt blocks ret ctx -> [Some (Reg ctx)]
termStmtRegs (Jump tgt) = jumpTargetRegs tgt
termStmtRegs (Br cond tgt1 tgt2) =
  Some cond : jumpTargetRegs tgt1 ++ jumpTargetRegs tgt2
termStmtRegs (MaybeBranch _ cond stgt tgt) =
  Some cond : switchTargetRegs stgt ++ jumpTargetRegs tgt
termStmtRegs (VariantElim _ cond stgts) =
  Some cond : foldMapFC switchTargetRegs stgts
termStmtRegs (Return reg) = [Some reg]
termStmtRegs (TailCall reg _ regs) =
  Some reg : foldMapFC (\r -> [Some r]) regs
termStmtRegs (ErrorStmt reg) = [Some reg]
