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

module SAWScript.Heapster.SAWTranslation where

import Data.Maybe
import Data.Kind
import GHC.TypeLits
import qualified Data.Functor.Constant as Constant
import Control.Lens hiding ((:>),Index)
import Control.Monad.Reader
import Control.Monad.Cont

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty, take, view)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.Analysis.Fixpoint.Components

import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor

import SAWScript.Heapster.CruUtil
import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Implication
import SAWScript.Heapster.TypedCrucible


-- | FIXME HERE: move to Hobbits!
mapRListTail :: MapRList f (ctx :> a) -> MapRList f ctx
mapRListTail (xs :>: _) = xs


----------------------------------------------------------------------
-- * The Type and Expression Translation Monad
----------------------------------------------------------------------

-- | The result of translating a 'PermExpr' at 'CrucibleType' @a@. This is a
-- form of partially static data in the sense of partial evaluation.
data ExprTrans (a :: CrucibleType) where
  -- | LLVM pointers have their translations dictated by their permissions, so
  -- the translations of their expressions have no computational content
  ETrans_LLVM :: ExprTrans (LLVMPointerType w)

  -- | Frames also have no computational content
  ETrans_LLVMFrame :: ExprTrans (LLVMFrameType w)

  -- | Lifetimes also have no computational content
  ETrans_Lifetime :: ExprTrans LifetimeType

  -- | Permission lists also have no computational content
  ETrans_PermList :: ExprTrans PermListType

  -- | The default translation of an expression is just a SAW term
  ETrans_Term :: OpenTerm -> ExprTrans a


-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx (ctx :: RList CrucibleType) = MapRList ExprTrans ctx

-- | Build the correct 'ExprTrans' from an 'OpenTerm' given its type
mkExprTrans :: TypeRepr a -> OpenTerm -> ExprTrans a
mkExprTrans = helper where
  helper :: TypeRepr a -> OpenTerm -> ExprTrans a
  helper (LLVMPointerRepr _) _ = ETrans_LLVM
  helper (LLVMFrameRepr _) _ = ETrans_LLVMFrame
  helper LifetimeRepr _ = ETrans_Lifetime
  helper PermListRepr _ = ETrans_PermList
  helper _ t = ETrans_Term t

-- | Map an expression translation result to an 'OpenTerm' or 'Nothing' if it
-- has no pure content, i.e., if it is a splitting or LLVM value
exprTransToTerm :: ExprTrans a -> OpenTerm
exprTransToTerm ETrans_LLVM = unitOpenTerm
exprTransToTerm ETrans_LLVMFrame = unitOpenTerm
exprTransToTerm ETrans_Lifetime = unitOpenTerm
exprTransToTerm ETrans_PermList = unitOpenTerm
exprTransToTerm (ETrans_Term t) = t

-- | Map a context of pure translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones that are always translated to unit
exprCtxToTerms :: ExprTransCtx ctx -> [OpenTerm]
exprCtxToTerms =
  mapRListToList . mapMapRList (Constant.Constant . exprTransToTerm)

-- | Translate a variable to a 'Member' proof, raising an error if the variable
-- is unbound
translateVar :: Mb ctx (ExprVar a) -> Member ctx a
translateVar mb_x | Left memb <- mbNameBoundP mb_x = memb
translateVar _ = error "translateVar: unbound variable!"


-- | The type translation monad = a reader monad for 'ExprTransCtx'
type TypeTransM ctx = Reader (ExprTransCtx ctx)

-- | Run a 'TypeTransM' computation in an extended context
inExtTypeTransM :: ExprTrans tp -> TypeTransM (ctx :> tp) a ->
                   TypeTransM ctx a
inExtTypeTransM tp_trans = withReader (:>: tp_trans)

-- | Apply the result of a translation to that of another
applyTransM :: Monad m => m OpenTerm -> m OpenTerm -> m OpenTerm
applyTransM m1 m2 = applyOpenTerm <$> m1 <*> m2

-- | Apply the result of a translation to the results of multiple translations
applyMultiTransM :: Monad m => m OpenTerm -> [m OpenTerm] -> m OpenTerm
applyMultiTransM m ms = foldl applyTransM m ms

-- | Build a lambda in a translation monad
lambdaTransM :: String -> OpenTerm -> (OpenTerm -> Reader r OpenTerm) ->
                Reader r OpenTerm
lambdaTransM x tp body_m =
  do r <- ask
     return $ lambdaOpenTerm x tp (\x -> runReader (body_m x) r)

-- | Build a pi in a translation monad
piTransM :: String -> OpenTerm -> (OpenTerm -> Reader r OpenTerm) ->
            Reader r OpenTerm
piTransM x tp body_m =
  do r <- ask
     return $ piOpenTerm x tp (\x -> runReader (body_m x) r)

-- | Build a let-binding in a translation monad
letTransM :: String -> OpenTerm -> Reader r OpenTerm ->
             (OpenTerm -> Reader r OpenTerm) ->
             Reader r OpenTerm
letTransM x tp rhs_m body_m =
  do r <- ask
     return $
       letOpenTerm x tp (runReader rhs_m r) (\x -> runReader (body_m x) r)


----------------------------------------------------------------------
-- * The Type and Expression Translation
----------------------------------------------------------------------

-- | The typeclass for the type-level translation
class TypeTranslate a res | a -> res where
  tptranslate :: Mb ctx a -> TypeTransM ctx res

instance TypeTranslate (NatRepr n) OpenTerm where
  tptranslate mb_n = return $ natOpenTerm $ mbLift $ fmap intValue mb_n

-- | Translate a Crucible type to a SAW type, converting 'Nothing' to unit
translateType :: Mb ctx (TypeRepr a) -> TypeTransM ctx OpenTerm
translateType mb_t = maybe unitTypeOpenTerm id <$> tptranslate mb_t

-- The Idea: if a type translates to Nothing then its expressions are not
-- represented in our SAW translation
instance TypeTranslate (TypeRepr a) (Maybe OpenTerm) where
  tptranslate [nuP| (AnyRepr) |] =
    return $ error "TypeTranslate: Any"
  tptranslate [nuP| (UnitRepr) |] =
    return $ Just unitTypeOpenTerm
  tptranslate [nuP| (BoolRepr) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.Bool" []
  tptranslate [nuP| (NatRepr) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.Nat" []
  tptranslate [nuP| (IntegerRepr) |] =
    return $ error "TypeTranslate: IntegerRepr"
  tptranslate [nuP| (RealValRepr) |] =
    return $ error "TypeTranslate: RealValRepr"
  tptranslate [nuP| (ComplexRealRepr) |] =
    return $ error "TypeTranslate: ComplexRealRepr"
  tptranslate [nuP| (BVRepr w) |] =
    Just <$>
    applyOpenTerm (globalOpenTerm "Prelude.bitvector") <$> tptranslate w

  -- Our special-purpose intrinsic types, whose translations do not have
  -- computational content
  tptranslate [nuP| (LLVMPointerRepr _) |] =
    return Nothing
  tptranslate [nuP| (LLVMFrameRepr _) |] =
    return Nothing
  tptranslate [nuP| LifetimeRepr |] =
    return Nothing
  tptranslate [nuP| PermListRepr |] =
    return Nothing
  tptranslate [nuP| (IntrinsicRepr _ _) |] =
    return $ error "TypeTranslate: IntrinsicRepr"

  tptranslate [nuP| (RecursiveRepr _ _) |] =
    return $ error "TypeTranslate: RecursiveRepr"
  tptranslate [nuP| (FloatRepr _) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.Float" []
  tptranslate [nuP| (IEEEFloatRepr _) |] =
    return $ error "TypeTranslate: IEEEFloatRepr"
  tptranslate [nuP| (CharRepr) |] =
    return $ error "TypeTranslate: CharRepr"
  tptranslate [nuP| (StringRepr) |] =
    return $ Just $ dataTypeOpenTerm "Prelude.String" []
  tptranslate [nuP| (FunctionHandleRepr _ _) |] =
    -- NOTE: function permissions translate to the SAW function, but the
    -- function handle itself has no SAW translation
    return Nothing
  tptranslate [nuP| (MaybeRepr tp) |] =
    fmap (applyOpenTerm (globalOpenTerm "Prelude.Maybe")) <$> tptranslate tp
  tptranslate [nuP| (VectorRepr _) |] =
    return $ error "TypeTranslate: VectorRepr (can't map to Vec without size)"
  tptranslate [nuP| (StructRepr _) |] =
    return $ error "TypeTranslate: StructRepr"
  tptranslate [nuP| (VariantRepr _) |] =
    return $ error "TypeTranslate: VariantRepr"
  tptranslate [nuP| (ReferenceRepr _) |] =
    return $ error "TypeTranslate: ReferenceRepr"
  tptranslate [nuP| (WordMapRepr _ _) |] =
    return $ error "TypeTranslate: WordMapRepr"
  tptranslate [nuP| (StringMapRepr _) |] =
    return $ error "TypeTranslate: StringMapRepr"
  tptranslate [nuP| (SymbolicArrayRepr _ _) |] =
    return $ error "TypeTranslate: SymbolicArrayRepr"
  tptranslate [nuP| (SymbolicStructRepr _) |] =
    return $ error "TypeTranslate: SymbolicStructRepr"


instance TypeTranslate (ExprVar a) (ExprTrans a) where
  tptranslate mb_x = mapRListLookup (translateVar mb_x) <$> ask

-- | Translate a permission to a SAW type, converting 'Nothing' to unit
translatePerm :: Mb ctx (ValuePerm a) -> TypeTransM ctx OpenTerm
translatePerm mb_p = maybe unitTypeOpenTerm id <$> tptranslate mb_p

instance TypeTranslate (PermExpr a) (ExprTrans a) where
  tptranslate = error "FIXME HERE NOW"

instance ress ~ (CtxToRList as) =>
         TypeTranslate (PermExprs as) (ExprTransCtx ress) where
  tptranslate = error "FIXME HERE NOW"

instance TypeTranslate (BVFactor w) OpenTerm where
  tptranslate = error "FIXME HERE NOW"

-- [| p :: ValuePerm |] = type of the impl translation of reg with perms p
instance TypeTranslate (ValuePerm a) (Maybe OpenTerm) where
  tptranslate = error "FIXME HERE NOW"

instance TypeTranslate (ValuePerms a) [OpenTerm] where
  tptranslate = error "FIXME HERE NOW"


----------------------------------------------------------------------
-- * The Translations of Permission Implications
----------------------------------------------------------------------

-- | The result of translating a "proof element" of a permission of type
-- @'ValuePerm' a@. The idea here is that, for a permission implication or typed
-- statement that consumes or emits permission @p@, the translation consumes or
-- emits an element of the SAW type @'tptranslate' p@.
--
-- Another way to look at a @'PermTrans'@ for permission @p@ is that it is a
-- partially static representation (in the sense of the partial evaluation
-- literature) of a SAW expression of type @'tptranslate' p@. Note that we do
-- not include special representations for disjunctions, existentials, or
-- recursive mu permissions, however, because our type-checker does not
-- generally introduce these forms as intermediate values.
data PermTrans ctx (a :: CrucibleType) where
  -- | An @eq(e)@ permission has no computational content
  PTrans_Eq :: Mb ctx (PermExpr a) -> PermTrans ctx a

  -- | A conjuction of atomic permission translations; note that the 'MapRList'
  -- argument is so we know our @ctx@ argument is well-formeds
  PTrans_Conj :: MapRList Proxy ctx -> [AtomicPermTrans ctx a] ->
                 PermTrans ctx a

  -- | The default translation is a SAW term. Note that this can include LLVM
  -- pointer permissions that have not yet been broken into multiple SAW terms.
  PTrans_Term :: Mb ctx (ValuePerm a) -> OpenTerm -> PermTrans ctx a


-- | The 'PermTrans' type for atomic permissions
data AtomicPermTrans ctx a where

  -- | The translation of an LLVM field permission is just the translation of
  -- its contents
  APTrans_LLVMField :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMFieldPerm w) ->
                       PermTrans ctx (LLVMPointerType w) ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM free permissions have no computational content
  APTrans_LLVMFree :: (1 <= w, KnownNat w) =>
                      Mb ctx (PermExpr (BVType w)) ->
                      AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM frame permissions have no computational content
  APTrans_LLVMFrame :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMFramePerm w) ->
                       AtomicPermTrans ctx (LLVMFrameType w)

  -- | Lifetime permissions have no computational content
  APTrans_LifetimePerm :: Mb ctx (AtomicPerm LifetimeType) ->
                          AtomicPermTrans ctx LifetimeType

  -- | Propositional permissions have no computational content
  APTrans_BVProp :: (1 <= w, KnownNat w) => Mb ctx (BVProp w) ->
                    AtomicPermTrans ctx (LLVMPointerType w)

  -- | The default translation of an atomic permission is a SAW term
  APTrans_Term :: Mb ctx (AtomicPerm a) -> OpenTerm -> AtomicPermTrans ctx a


-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = MapRList (PermTrans ctx) ps

-- | Build a 'PermTrans' from a permission and its term
mkPermTrans :: Mb ctx (ValuePerm a) -> OpenTerm -> PermTrans ctx a
mkPermTrans [nuP| ValPerm_Eq mb_e |] _ = PTrans_Eq mb_e
mkPermTrans mb_p t = PTrans_Term mb_p t

-- | Map a perm translation result to an 'OpenTerm'
permTransToTerm :: PermTrans ctx a -> OpenTerm
permTransToTerm (PTrans_Eq _) = unitOpenTerm
permTransToTerm (PTrans_Conj _ aps) =
  tupleOpenTerm $ map atomicPermTransToTerm aps
permTransToTerm (PTrans_Term _ t) = t

-- | Map an atomic perm translation result to an 'OpenTerm'
atomicPermTransToTerm :: AtomicPermTrans ctx a -> OpenTerm
atomicPermTransToTerm _ = error "FIXME HERE NOW"

-- | Map a context of perm translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones that are always translated to unit
permCtxToTerms :: PermTransCtx ctx ps -> [OpenTerm]
permCtxToTerms =
  mapRListToList . mapMapRList (Constant.Constant . permTransToTerm)

-- | Extract out the permission of a permission translation result
permTransPerm :: PermTrans ctx a -> Mb ctx (ValuePerm a)
permTransPerm (PTrans_Eq e) = fmap ValPerm_Eq e
permTransPerm (PTrans_Conj prxs ts) =
  fmap ValPerm_Conj $ foldr (mbMap2 (:)) (nuMulti prxs $ const []) $
  map atomicPermTransPerm ts
permTransPerm (PTrans_Term p _) = p

atomicPermTransPerm :: AtomicPermTrans ctx a -> Mb ctx (AtomicPerm a)
atomicPermTransPerm = error "FIXME HERE NOW"

extMb :: Mb ctx a -> Mb (ctx :> tp) a
extMb = mbCombine . fmap (nu . const)

-- | Extend the context of a permission translation result
extPermTrans :: PermTrans ctx a -> PermTrans (ctx :> tp) a
extPermTrans (PTrans_Eq e) = PTrans_Eq $ extMb e
extPermTrans (PTrans_Conj prxs aps) =
  PTrans_Conj (prxs :>: Proxy) (map extAtomicPermTrans aps)
extPermTrans (PTrans_Term p t) = PTrans_Term (extMb p) t

-- | Extend the context of an atomic permission translation result
extAtomicPermTrans :: AtomicPermTrans ctx a -> AtomicPermTrans (ctx :> tp) a
extAtomicPermTrans = error "FIXME HERE NOW"

-- | Extend the context of a permission translation context
extPermTransCtx :: PermTransCtx ctx ps -> PermTransCtx (ctx :> tp) ps
extPermTransCtx = mapMapRList extPermTrans

-- | Add another permission translation to a permission translation context
consPermTransCtx :: PermTransCtx ctx ps -> PermTrans ctx a ->
                    PermTransCtx ctx (ps :> a)
consPermTransCtx = (:>:)


----------------------------------------------------------------------
-- * The Implication Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to its corresponding SAW variable that is
-- bound to its translation
data TypedEntryTrans ext blocks ret args =
  TypedEntryTrans (TypedEntry ext blocks ret args) OpenTerm

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks ret args =
  TypedBlockTrans [TypedEntryTrans ext blocks ret args]

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks ret =
  MapRList (TypedBlockTrans ext blocks ret) blocks

-- | Translate an entrypoint ID by looking up its SAW function
translateTypedEntryID :: TypedEntryID blocks args ghosts ->
                         TypedBlockMapTrans ext blocks ret ->
                         OpenTerm
translateTypedEntryID entryID blkMap =
  let TypedBlockTrans entries = mapRListLookup (entryBlockID entryID) blkMap in
  foldr (\(TypedEntryTrans entry trm) rest ->
          case entry of
            TypedEntry entryID' _ _ _
              | Just Refl <- testEquality entryID entryID' -> trm
            _ -> rest)
  (error "translateTypedEntryID")
  entries


-- | Contextual info for an implication translation
data ImpTransInfo ext blocks ret args ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiPermStackVars :: MapRList (Member ctx) ps,
    itiBlockTrans :: TypedBlockMapTrans ext blocks ret,
    itiCatchHandler :: OpenTerm,
    itiReturnType :: OpenTerm
  }

-- | Return the default catch handler of a given return type, which is just a
-- call to @errorM@ at that type
defaultCatchHandler :: OpenTerm -> OpenTerm
defaultCatchHandler = applyOpenTerm (globalOpenTerm "Prelude.errorM")

-- | Extend the context of an 'ImpTransInfo'
extPermTransInfo :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                    ImpTransInfo ext blocks ret args ps ctx ->
                    ImpTransInfo ext blocks ret args ps (ctx :> tp)
extPermTransInfo tp_trans perm_trans (ImpTransInfo {..}) =
  ImpTransInfo
  { itiExprCtx = itiExprCtx :>: tp_trans
  , itiPermCtx = consPermTransCtx (extPermTransCtx itiPermCtx) perm_trans
  , itiPermStack = extPermTransCtx itiPermStack
  , itiPermStackVars = mapMapRList Member_Step itiPermStackVars
  , .. }

-- | The monad for translating permission implications
type ImpTransM ext blocks ret args ps ctx =
  Reader (ImpTransInfo ext blocks ret args ps ctx)

-- | Embed a type translation into an impure translation
tpTransM :: TypeTransM ctx a -> ImpTransM ext blocks ret args ps ctx a
tpTransM = withReader itiExprCtx

-- | Run an 'ImpTransM' computation in an extended context
inExtImpTransM :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                  ImpTransM ext blocks ret args ps (ctx :> tp) a ->
                  ImpTransM ext blocks ret args ps ctx a
inExtImpTransM tp_trans perm_trans =
  withReader $ extPermTransInfo tp_trans perm_trans

-- | Get the top permission on the stack
getTopPermM :: ImpTransM ext blocks ret args (ps :> tp) ctx (PermTrans ctx tp)
getTopPermM = (\(_ :>: p) -> p) <$> itiPermStack <$> ask

-- | Apply a transformation to the (translation of the) current perm stack
withPermStackM :: (MapRList (Member ctx) ps_in -> MapRList (Member ctx) ps_out) ->
                  (PermTransCtx ctx ps_in -> PermTransCtx ctx ps_out) ->
                  ImpTransM ext blocks ret args ps_out ctx a ->
                  ImpTransM ext blocks ret args ps_in ctx a
withPermStackM f_vars f_p =
  withReader $ \info ->
  info { itiPermStack = f_p (itiPermStack info),
         itiPermStackVars = f_vars (itiPermStackVars info) }

-- | Assert a property of the current permission stack, raising an 'error' if it
-- fails to hold. The 'String' names the construct being translated.
assertPermStackM :: String -> (MapRList (Member ctx) ps ->
                               PermTransCtx ctx ps -> Bool) ->
                    ImpTransM ext blocks ret args ps ctx ()
assertPermStackM nm f =
  ask >>= \info ->
  if f (itiPermStackVars info) (itiPermStack info) then return () else
    error ("translate: " ++ nm)

-- | Assert that the top permission is as given by the arguments
assertTopPermM :: String -> Mb ctx (ExprVar a) -> Mb ctx (ValuePerm a) ->
                  ImpTransM ext blocks ret args (ps :> a) ctx ()
assertTopPermM nm x p =
  assertPermStackM nm (\(_ :>: x_top) (_ :>: p_top) ->
                        x_top == translateVar x && permTransPerm p_top == p)

-- | Get the (translation of the) perms for a variable
getVarPermM :: Mb ctx (ExprVar tp) ->
               ImpTransM ext blocks ret args ps ctx (PermTrans ctx tp)
getVarPermM x = mapRListLookup (translateVar x) <$> itiPermCtx <$> ask

-- | Assert that a variable has a given permission
assertVarPermM :: String -> Mb ctx (ExprVar tp) -> Mb ctx (ValuePerm tp) ->
                  ImpTransM ext blocks ret args ps ctx ()
assertVarPermM nm x p =
  getVarPermM x >>= \x_p ->
  if permTransPerm x_p == p then return () else error ("translation: " ++ nm)

-- | Set the (translation of the) perms for a variable in a computation
setVarPermM :: Mb ctx (ExprVar tp) -> PermTrans ctx tp ->
               ImpTransM ext blocks ret args ps ctx a ->
               ImpTransM ext blocks ret args ps ctx a
setVarPermM x p =
  local $ \info -> info { itiPermCtx =
                            mapRListSet (translateVar x) p $ itiPermCtx info }

-- | Build the monadic return type @CompM ret@, where @ret@ is the current
-- return type in 'itiReturnType'
compReturnTypeM :: ImpTransM ext blocks ret args ps_out ctx OpenTerm
compReturnTypeM =
  applyOpenTerm (globalOpenTerm "Prelude.CompM") <$> itiReturnType <$> ask

-- | Run a computation with a new catch handler
withCatchHandlerM :: OpenTerm -> ImpTransM ext blocks ret args ps_out ctx a ->
                     ImpTransM ext blocks ret args ps_out ctx a
withCatchHandlerM h = local (\info -> info { itiCatchHandler = h })

-- | Apply the translation of a function-like construct (i.e., a
-- 'TypedJumpTarget' or 'TypedFnHandle') to the pure plus impure translations of
-- its arguments
--
-- FIXME HERE NOW: should take in a CruCtx for the types, and possibly a
-- DistPerms for the arguments
translateApply :: OpenTerm -> ExprTransCtx tps -> PermTransCtx ctx tps ->
                  OpenTerm
translateApply f p_args i_args =
  applyOpenTermMulti f (exprCtxToTerms p_args ++ permCtxToTerms i_args)


-- | The typeclass for translating permission implications
class ImplTranslate a res ext blocks ret args ps ctx | ctx a -> res where
  itranslate :: Mb ctx a -> ImpTransM ext blocks ret args ps ctx res

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks ret args where
  itranslateF :: Mb ctx (f ps) -> ImpTransM ext blocks ret args ps ctx OpenTerm


-- Translate a TypeRepr to a SAW type in the implication translation monad,
-- using the unit type in place of 'Nothing'
instance ImplTranslate (TypeRepr a) OpenTerm ext blocks ret args ps ctx where
  itranslate tp = maybe unitTypeOpenTerm id <$> tpTransM (tptranslate tp)

-- Translate a permission to a SAW type in the implication translation monad,
-- using the unit type in place of 'Nothing'
instance ImplTranslate (ValuePerm a) OpenTerm ext blocks ret args ps ctx where
  itranslate p = maybe unitTypeOpenTerm id <$> tpTransM (tptranslate p)


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

-- | FIXME: figure out a better name and move to Hobbits
mbMap2 :: (a -> b -> c) -> Mb ctx a -> Mb ctx b -> Mb ctx c
mbMap2 f mb1 mb2 = fmap f mb1 `mbApply` mb2

-- | Translate a 'SimplImpl' to a function on translation computations
itranslateSimplImpl :: Proxy ps -> Mb ctx (SimplImpl ps_in ps_out) ->
                       ImpTransM ext blocks ret args (ps :++: ps_out) ctx res ->
                       ImpTransM ext blocks ret args (ps :++: ps_in) ctx res

itranslateSimplImpl _ [nuP| SImpl_Drop x p |] m =
  assertTopPermM "SImpl_Drop" x p >>
  withPermStackM (\(xs :>: _) -> xs) (\(ps :>: _) -> ps) m

itranslateSimplImpl _ [nuP| SImpl_IntroOrL x p1 p2 |] m =
  do assertTopPermM "SImpl_IntroOrL" x p1
     tp1 <- itranslate p1
     tp2 <- itranslate p2
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: (PTrans_Term (mbMap2 ValPerm_Or p1 p2)
                 (ctorOpenTerm "Prelude.Left"
                  [tp1, tp2, permTransToTerm p_top])))
       m

itranslateSimplImpl _ [nuP| SImpl_IntroOrR x p1 p2 |] m =
  do assertTopPermM "SImpl_IntroOrR" x p2
     tp1 <- itranslate p1
     tp2 <- itranslate p2
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: (PTrans_Term (mbMap2 ValPerm_Or p1 p2)
                 (ctorOpenTerm "Prelude.Right"
                  [tp1, tp2, permTransToTerm p_top])))
       m

itranslateSimplImpl _ [nuP| SImpl_IntroExists x (e :: PermExpr tp) p |] m =
  do assertTopPermM "SImpl_IntroExists" x
       (mbMap2 subst (fmap singletonSubst e) p)
     let tp :: TypeRepr tp = knownRepr
     tp_trans <- itranslate $ nuMulti (mbToProxy e) $ const tp
     tp_f <- tpTransM $ lambdaTransM "x_introEx" tp_trans $ \z ->
         inExtTypeTransM (mkExprTrans tp z) (translatePerm $ mbCombine p)
     e_trans <- exprTransToTerm <$> tpTransM (tptranslate e)
     withPermStackM id
       (\(ps :>: p_top) ->
         ps :>: (PTrans_Term (fmap ValPerm_Exists p)
                 (ctorOpenTerm "Prelude.exists"
                  [tp_trans, tp_f, e_trans, permTransToTerm p_top])))
       m

itranslateSimplImpl _ _ _ = error "FIXME HERE NOW: finish itranslateSimplImpl!"


-- | Translate a 'PermImpl1' to a function on translation computations
itranslatePermImpl1 :: ImplTranslateF r ext blocks ret args =>
                       Mb ctx (PermImpl1 ps_in ps_outs) ->
                       Mb ctx (MbPermImpls r ps_outs) ->
                       ImpTransM ext blocks ret args ps_in ctx OpenTerm

-- A failure translates to a call to the catch handler, which is the most recent
-- Impl1_Catch, if one exists, or the SAW errorM function otherwise
itranslatePermImpl1 [nuP| Impl1_Fail |] _ = itiCatchHandler <$> ask

-- A catch runs the first computation using the second as catch handler
itranslatePermImpl1 [nuP| Impl1_Catch |]
  [nuP| MbPermImpls_Cons (MbPermImpls_Cons _ mb_impl1) mb_impl2 |] =
  do compMType <- compReturnTypeM
     letTransM "catchpoint" compMType
       (itranslate $ mbCombine mb_impl2)
       (\handler -> withCatchHandlerM handler $ itranslate $ mbCombine mb_impl1)

-- A push moves the given permission from x to the top of the perm stack
itranslatePermImpl1 [nuP| Impl1_Push x p |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  assertVarPermM "Impl1_Push" x p >>
  getVarPermM x >>= \ptrans ->
  setVarPermM x (PTrans_Conj (mbToProxy p) [])
  (withPermStackM (:>: translateVar x) (:>: ptrans) $
   itranslate (mbCombine mb_impl))

-- A pop moves the given permission from the top of the perm stack to x
itranslatePermImpl1 [nuP| Impl1_Pop x p |] [nuP| MbPermImpls_Cons _ mb_impl |] =
  assertTopPermM "Impl1_Pop" x p >>
  assertVarPermM "Impl1_Pop" x (nuMulti (mbToProxy p) $ const ValPerm_True) >>
  getTopPermM >>= \ptrans ->
  setVarPermM x ptrans
  (withPermStackM mapRListTail mapRListTail $
   itranslate (mbCombine mb_impl))

-- An or elimination performs a pattern-match on an Either
itranslatePermImpl1 [nuP| Impl1_ElimOr x p1 p2 |]
  [nuP| MbPermImpls_Cons (MbPermImpls_Cons _ mb_impl1) mb_impl2 |] =
  do assertTopPermM "Impl1_ElimOr" x (mbMap2 ValPerm_Or p1 p2)
     tp1 <- itranslate p1
     tp2 <- itranslate p2
     tp_ret <- compReturnTypeM
     ptrans <- permTransToTerm <$> getTopPermM
     applyMultiTransM (return $ globalOpenTerm "Prelude.either")
       [ return tp1, return tp2, return tp_ret
       , lambdaTransM "x_left" tp1
         (\z ->
           withPermStackM id ((:>: mkPermTrans p1 z) . mapRListTail) $
           itranslate $ mbCombine mb_impl1)
       , lambdaTransM "x_right" tp2
         (\z ->
           withPermStackM id ((:>: mkPermTrans p2 z) . mapRListTail) $
           itranslate $ mbCombine mb_impl2)
       , return ptrans]

-- An existential elimination performs a pattern-match on a Sigma
itranslatePermImpl1 [nuP| Impl1_ElimExists x (p :: Binding tp (ValuePerm a)) |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  do assertTopPermM "Impl1_ElimExists" x (fmap ValPerm_Exists p)
     let tp :: TypeRepr tp = knownRepr
     tp_trans <- itranslate $ nuMulti (mbToProxy x) $ const tp
     tp_f <- tpTransM $ lambdaTransM "x_elimEx" tp_trans $ \z ->
       inExtTypeTransM (mkExprTrans tp z) (translatePerm $ mbCombine p)
     ret_f <- lambdaTransM "x_elimEx" tp_trans $ const compReturnTypeM
     ptrans <- permTransToTerm <$> getTopPermM
     applyMultiTransM (return $ globalOpenTerm "Prelude.Sigma__rec")
       [ return tp_trans, return tp_f, return ret_f
       , lambdaTransM "x1_elimEx" tp_trans
         (\z1 ->
           lambdaTransM "x2_elimEx" (applyOpenTerm tp_f z1) $ \z2 ->
           inExtImpTransM (mkExprTrans tp z1)
           (PTrans_Conj (mbToProxy $ mbCombine p) []) $
           withPermStackM id ((:>: mkPermTrans (mbCombine p) z2) . mapRListTail) $
           itranslate $ mbCombine mb_impl)
       , return ptrans ]

-- A SimplImpl is translated using itranslateSimplImpl
itranslatePermImpl1 [nuP| Impl1_Simpl simpl prx |]
  [nuP| MbPermImpls_Cons _ mb_impl |] =
  itranslateSimplImpl (mbLift prx) simpl $ itranslate $ mbCombine mb_impl

itranslatePermImpl1 _ _ = error "FIXME HERE NOW: finish itranslatePermImpl1!"


instance ImplTranslateF r ext blocks ret args =>
         ImplTranslate (PermImpl r ps) OpenTerm ext blocks ret args ps ctx where
  itranslate [nuP| PermImpl_Done r |] = itranslateF r
  itranslate [nuP| PermImpl_Step impl1 mb_impls |] =
    itranslatePermImpl1 impl1 mb_impls


{-

-- | FIXME: figure out a better name and move to Hobbits
mbMap2 :: (a -> b -> c) -> Mb ctx a -> Mb ctx b -> Mb ctx c
mbMap2 f mb1 mb2 = fmap f mb1 `mbApply` mb2

-- | Apply left or-introduction to a permission translation by applying the
-- @Left@ constructor in SAW
introOrLTrans :: Mb ctx (ValuePerm a) -> PermTrans ctx a ->
                 ImpTransM ext blocks ret args ps ctx (PermTrans ctx a)
introOrLTrans p1 pt =
  do tp1 <- tpTransM $ tptranslate p1
     tp2 <- tpTransM $ tptranslate (permTransPerm pt)
     return $
       PTrans_Term (mbMap2 ValPerm_Or p1 $ permTransPerm pt)
       (ctorOpenTerm "Prelude.Left" [tp1, tp2, permTransToTerm pt])

-- | Apply right or-introduction to a permission translation by applying the
-- @Right@ constructor in SAW
introOrRTrans :: Mb ctx (ValuePerm a) -> PermTrans ctx a ->
                 ImpTransM ext blocks ret args ps ctx (PermTrans ctx a)
introOrRTrans p2 pt =
  do tp1 <- tpTransM $ tptranslate (permTransPerm pt)
     tp2 <- tpTransM $ tptranslate p2
     return $
       PTrans_Term (mbMap2 ValPerm_Or (permTransPerm pt) p2)
       (ctorOpenTerm "Prelude.Right" [tp1, tp2, permTransToTerm pt])

-- | Translate an or-elimination to the @either@ elimination rule
elimOrTrans :: PermTrans ctx a ->
               (PermTrans ctx a ->
                ImpTransM ext blocks ret args ps ctx OpenTerm) ->
               (PermTrans ctx a ->
                ImpTransM ext blocks ret args ps ctx OpenTerm) ->
               ImpTransM ext blocks ret args ps ctx OpenTerm
elimOrTrans (PTrans_Term mb_p t) f1 f2 =
  do let mb_p1 = fmap orPermLeft mb_p
         mb_p2 = fmap orPermRight mb_p
     tp1 <- tpTransM $ tptranslate mb_p1
     tp2 <- tpTransM $ tptranslate mb_p2
     ret_tp <- itiReturnType <$> ask
     f1trans <- lambdaTransM "x_left" tp1 (f1 . mkPermTrans mb_p1)
     f2trans <- lambdaTransM "x_right" tp2 (f2 . mkPermTrans mb_p2)
     return (applyOpenTermMulti (globalOpenTerm "Prelude.either")
             [tp1, tp2, ret_tp, f1trans, f2trans])
elimOrTrans _ _ _ = error "elimOrTrans"

-- | Translate an exists-introduction to a @Sigma@ introduction
introExistsTrans :: KnownRepr TypeRepr tp => Mb ctx (PermExpr tp) ->
                    Mb ctx (Binding tp (ValuePerm a)) ->
                    PermTrans ctx a ->
                    ImpTransM ext blocks ret args ps ctx (PermTrans ctx a)
introExistsTrans (mb_e :: Mb ctx (PermExpr tp)) mb_p_body pt
  | permTransPerm pt
    == mbMap2 (\e p_body ->
                subst (singletonSubst e) p_body) mb_e mb_p_body =
    do let mb_p = permTransPerm pt
           t = permTransToTerm pt
       let tp = knownRepr :: TypeRepr tp
       tp_trans <- tpTransM $ tptranslate (fmap (const tp) mb_e)
       tp_f <- tpTransM $ lambdaTransM "x_introEx" tp_trans $ \x ->
         inExtTypeTransM (mkExprTrans tp x) (tptranslate $ mbCombine mb_p_body)
       e <- exprTransToTerm <$> tpTransM (tptranslate mb_e)
       return $
         PTrans_Term (fmap ValPerm_Exists mb_p_body) $
         ctorOpenTerm "Prelude.exists" [tp_trans, tp_f, e, t]
introExistsTrans _ _ _ = error "introExistsTrans"

-- | Translate an existential elimination into a @Sigma@ elimination
elimExistsTrans :: KnownRepr TypeRepr tp =>
                   PermTrans ctx a ->
                   (PermTrans (ctx :> tp) a ->
                    ImpTransM ext blocks ret args ps (ctx :> tp) OpenTerm) ->
                   ImpTransM ext blocks ret args ps ctx OpenTerm
elimExistsTrans (PTrans_Term mb_p t) f =
  do let tp1 = knownRepr
         mb_p_body = mbCombine $ fmap (exPermBody tp1) mb_p
     tp1_trans <- tpTransM $ tptranslate $ fmap (const tp1) mb_p
     tp2_trans <- tpTransM $ lambdaTransM "x_fst" tp1_trans $ \x ->
       inExtTypeTransM (mkExprTrans tp1 x) $ tptranslate mb_p_body
     ret_tp <- itiReturnType <$> ask
     let ret_tp_f = lambdaOpenTerm "x_fst" tp1_trans (const ret_tp)
     f_trans <- lambdaTransM "x_fst" tp1_trans $ \x1 ->
       lambdaTransM "x_snd" (applyOpenTerm tp2_trans x1) $ \x2 ->
       inExtImpTransM (mkExprTrans tp1 x1) (PTrans_True (mbToProxy mb_p_body)) $
       f (mkPermTrans mb_p_body x2)
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.Sigma__rec")
       [tp1_trans, tp2_trans, ret_tp_f, f_trans, t]
elimExistsTrans _ _ = error "elimExistsTrans"


----------------------------------------------------------------------
-- * The Implication Translation
----------------------------------------------------------------------

instance ImplTranslate1 f ext blocks ret args ps ctx =>
         ImplTranslate (PermImpl f ps) OpenTerm ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImplTranslate (TypedReg tp) (PermTrans ctx tp)
         ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImplTranslate (TypedExpr ext tp) (PermTrans ctx tp)
         ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImplTranslate (TypedEntryID blocks args' ghosts) OpenTerm
         ext blocks ret args ps ctx where
  itranslate mb_entryID =
    translateTypedEntryID (mbLift mb_entryID) <$> itiBlockTrans <$> ask

-- A sequence of distinguished permissions on variables translates to a list of
-- pure translations of the variables and impure translations of the permissions
-- on them
instance ImplTranslate (DistPerms tps) (ExprTransCtx tps, PermTransCtx ctx tps)
         ext blocks ret args ps ctx where
  itranslate [nuP| DistPermsNil |] = return (MNil, MNil)
  itranslate [nuP| DistPermsCons perms x _ |] =
    do (p_trs,i_trs) <- itranslate perms
       p_tr <- tpTransM $ tptranslate x
       i_tr <- itranslate (fmap TypedReg x)
       return (p_trs :>: p_tr, i_trs :>: i_tr)

instance ImplTranslate (TypedJumpTarget blocks ps) OpenTerm
         ext blocks ret args ps ctx where
  itranslate [nuP| TypedJumpTarget entryID _ perms |] =
    do f <- itranslate entryID
       (p_args, i_args) <- itranslate perms
       return $ translateApply f p_args i_args

{-
FIXME HERE NOW:
- Write the translation for PermImpl and for TypedStmt, to see what prims we need
- Need something special for TypedStmt to bind vars; maybe just do seqs?
- ImpTranslate for statement sequences, blocks / entrypoints, and CFGs
-}
-}
