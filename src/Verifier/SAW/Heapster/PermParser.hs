{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}

module Verifier.SAW.Heapster.PermParser where

import Data.List
import Data.String
import Data.Maybe
import Data.Functor.Product
import Data.Functor.Constant
import Data.Functor.Compose
import Data.Type.Equality
import GHC.TypeLits
import Control.Monad.Fail (MonadFail)
import qualified Control.Monad.Fail as Fail
import Control.Monad.Identity
import Control.Monad.Reader
import qualified Data.Type.RList as RL
import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind

import Text.Parsec
import Text.Parsec.Error
-- import Text.ParserCombinators.Parsec
import Prettyprinter hiding (comma, space)

import Data.Parameterized.Context hiding ((:>), empty, take, zipWith, Empty)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some
import Data.Parameterized.TraversableF
import Data.Parameterized.BoolRepr

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.FunctionHandle
-- import What4.FunctionName

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions


-- FIXME: maybe some of these should use unsafeMbTypeRepr for efficiency?
$(mkNuMatching [t| SourcePos |])
$(mkNuMatching [t| Message |])
$(mkNuMatching [t| ParseError |])
$(mkNuMatching [t| forall s u. (NuMatching s, NuMatching u) => State s u |])
$(mkNuMatching [t| forall s u a. (NuMatching s, NuMatching u, NuMatching a) =>
                Reply s u a |])
$(mkNuMatching [t| forall a. NuMatching a => Consumed a |])
$(mkNuMatching [t| forall a. NuMatching a => Identity a |])
$(mkNuMatching [t| forall f g a. NuMatching (f (g a)) => Compose f g a |])

instance Closable ParseError where
  toClosed = unsafeClose

instance Liftable ParseError where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable SourcePos where
  toClosed = unsafeClose

instance Liftable SourcePos where
  mbLift = unClosed . mbLift . fmap toClosed


----------------------------------------------------------------------
-- * The Parsing Monad and Parsing Utilities
----------------------------------------------------------------------

-- FIXME HERE: replace all calls to show tp with our own type-printing function
-- that prints in the same format that we are parsing


-- | An element of some representation type functor @f a@ along with a
-- 'TypeRepr' for @a@
data Typed f a = Typed (TypeRepr a) (f a)

-- | Try to cast an existential 'Typed' to a particular type
castTypedMaybe :: TypeRepr a -> Some (Typed f) -> Maybe (f a)
castTypedMaybe tp (Some (Typed tp' f))
  | Just Refl <- testEquality tp tp' = Just f
castTypedMaybe _ _ = Nothing

-- | A expression variable of some existentially quantified type
type SomeName = Some (Typed Name)

-- | A parsing environment, which includes variables and function names
data ParserEnv = ParserEnv {
  parserEnvExprVars :: [(String, SomeName)],
  parserEnvPermEnv :: PermEnv
}

-- | Make a 'ParserEnv' with empty contexts and a given list of function names
mkParserEnv :: PermEnv -> ParserEnv
mkParserEnv env = ParserEnv [] env

$(mkNuMatching [t| forall f a. NuMatching (f a) => Typed f a |])
$(mkNuMatching [t| ParserEnv |])

instance NuMatchingAny1 f => NuMatchingAny1 (Typed f) where
  nuMatchingAny1Proof = nuMatchingProof

-- | Look up an expression variable by name in a 'ParserEnv'
lookupExprVar :: String -> ParserEnv -> Maybe SomeName
lookupExprVar str = lookup str . parserEnvExprVars

{-
instance BindState String where
  bindState = mbLift

instance BindState ParserEnv where
  bindState [nuP| ParserEnv evars env |] =
    ParserEnv
    (mapMaybe (\env_elem -> case env_elem of
                  [nuP| (str, Some (Typed tp mb_n)) |]
                    | Right n <- mbNameBoundP mb_n ->
                      Just (mbLift str, Some (Typed (mbLift tp) n))
                  _ -> Nothing)
     (mbList evars))
    (mbLift env)
-}

-- | The parsing monad is a 'Parsec' computation with a 'ParserEnv'
type PermParseM s = Parsec s ParserEnv

-- | Functors that support name-binding
--
-- FIXME: is this the right interface? Maybe should be related to 'MonadBind'?
{-
class (Functor f, NuMatchingAny1 f) => FunctorBind f where
  mbF :: NuMatching a => Mb ctx (f a) -> f (Mb ctx a)

instance FunctorBind Consumed where
  mbF [nuP| Consumed a |] = Consumed a
  mbF [nuP| Empty a |] = Empty a

instance (BindState s, BindState u) => FunctorBind (Reply s u) where
  mbF [nuP| Ok a s err |] = Ok a (bindState s) (mbLift err)
  mbF [nuP| Error err |] = Error (mbLift err)

instance FunctorBind Identity where
  mbF [nuP| Identity a |] = Identity a

instance (FunctorBind f, FunctorBind g) => FunctorBind (Compose f g) where
  mbF [nuP| Compose fga |] = Compose $ fmap mbF $ mbF fga
-}

{-
instance (BindState s, BindState u) => BindState (State s u) where
  bindState [nuP| State s pos u |] =
    State (bindState s) (mbLift pos) (bindState u)
-}

-- | Lift a 'ParserEnv' out of a binding except for its 'PermEnv', which should
-- be unchanged from the input
liftParserEnv :: PermEnv -> Mb ctx ParserEnv -> ParserEnv
liftParserEnv env [nuP| ParserEnv evars _ |] =
  ParserEnv
  (mapMaybe (\env_elem -> case env_elem of
                [nuP| (str, Some (Typed tp mb_n)) |]
                  | Right n <- mbNameBoundP mb_n ->
                    Just (mbLift str, Some (Typed (mbLift tp) n))
                _ -> Nothing)
   (mbList evars))
  env

-- | Lift a Parsec 'State' out of a binding except for its 'PermEnv', which
-- should be unchanged from the input
liftParsecState :: Liftable s => PermEnv -> Mb ctx (State s ParserEnv) ->
                   State s ParserEnv
liftParsecState env [nuP| State s pos u |] =
  State (mbLift s) (mbLift pos) (liftParserEnv env u)

instance Liftable s => MonadBind (ParsecT s ParserEnv Identity) where
  mbM mb_m = mkPT $ \s ->
    let env = parserEnvPermEnv $ stateUser s in
    case fmap (flip runParsecT s) mb_m of
      [nuP| Identity (Consumed (Identity (Ok a s' err))) |] ->
        Identity (Consumed (Identity (Ok a (liftParsecState env s')
                                      (mbLift err))))
      [nuP| Identity (Consumed (Identity (Error err))) |] ->
        Identity (Consumed (Identity (Error (mbLift err))))
      [nuP| Identity (Consumed (Identity (Ok a s' err))) |] ->
        Identity (Empty (Identity (Ok a (liftParsecState env s')
                                   (mbLift err))))
      [nuP| Identity (Consumed (Identity (Error err))) |] ->
        Identity (Empty (Identity (Error (mbLift err))))

-- | Run a parsing computation in a context extended with an expression variable
withExprVar :: String -> TypeRepr tp -> ExprVar tp ->
               PermParseM s a -> PermParseM s a
withExprVar str tp x m =
  do env <- getState
     putState (env { parserEnvExprVars =
                       (str, Some (Typed tp x)) : parserEnvExprVars env})
     ret <- m
     putState env
     return ret

-- | Run a parsing computation in a context extended with 0 or more expression
-- variables
withExprVars :: RAssign (Constant String) ctx -> CruCtx ctx ->
                RAssign Name ctx ->
                PermParseM s a -> PermParseM s a
withExprVars MNil CruCtxNil MNil m = m
withExprVars (xs :>: Constant x) (CruCtxCons ctx tp) (ns :>: n) m =
  withExprVars xs ctx ns $ withExprVar x tp n m

-- | Cast an existential 'Typed' to a particular type or raise an error
castTypedM :: Stream s Identity Char =>
              String -> TypeRepr a -> Some (Typed f) ->
              PermParseM s (f a)
castTypedM _ tp (Some (Typed tp' f))
  | Just Refl <- testEquality tp tp' = return f
castTypedM str tp (Some (Typed tp' _)) =
  unexpected (str ++ " of type " ++ show tp') <?>
  (str ++ " of type " ++ show tp)

-- | Parse and skip at least one space
spaces1 :: Stream s Identity Char => PermParseM s ()
spaces1 = space >> spaces

-- | Apply a parsing computation to parse inside parentheses
parseInParens :: Stream s Identity Char =>
                 PermParseM s a -> PermParseM s a
parseInParens m =
  do char '('
     ret <- m
     spaces >> char ')'
     return ret

-- | Apply a parsing computation to parse inside optional parentheses
parseInParensOpt :: Stream s Identity Char =>
                    PermParseM s a -> PermParseM s a
parseInParensOpt m = parseInParens m <|> m


----------------------------------------------------------------------
-- * Parsing Types
----------------------------------------------------------------------

-- | Parse a comma
comma :: Stream s Identity Char => PermParseM s ()
comma = char ',' >> return ()

-- | Parse an integer
integer :: Stream s Identity Char => PermParseM s Integer
integer = read <$> many1 digit

-- | Parse an integer to a 'NatRepr'
parseNatRepr :: Stream s Identity Char =>
                PermParseM s (Some (Product NatRepr (LeqProof 1)))
parseNatRepr =
  do i <- integer
     case someNatGeq1 i of
       Just ret -> return ret
       Nothing -> unexpected "Zero bitvector width not allowed"

-- | Parse an integer to a 'NatRepr' and ensure it is a 'KnownNat' that is at
-- least one in the context of a call
parseKnownNatRepr :: Stream s Identity Char =>
                     (forall w. (1 <= w, KnownNat w) =>
                      NatRepr w -> PermParseM s a) ->
                     PermParseM s a
parseKnownNatRepr k =
  parseNatRepr >>= \case Some (Pair w LeqProof) -> withKnownNat w $ k w

-- | Parse a Crucible type and build a @'KnownRepr' 'TypeRepr'@ instance for it
--
-- FIXME: we would not need to use a 'KnownReprObj' here if we changed
-- 'ValPerm_Exists' to take its type argument as a normal 'TypeRepr' instead of
-- as a 'WithKnownRepr' constraint
parseTypeKnown :: Stream s Identity Char =>
                  PermParseM s (Some (KnownReprObj TypeRepr))
parseTypeKnown =
  spaces >>
  (parseInParens parseTypeKnown <|>
   (try (string "unit") >> return (Some $ mkKnownReprObj UnitRepr)) <|>
   (try (string "bool") >> return (Some $ mkKnownReprObj BoolRepr)) <|>
   (try (string "nat") >> return (Some $ mkKnownReprObj NatRepr)) <|>
   (do try (string "bv" >> spaces1)
       w <- parseNatRepr
       case w of
         Some (Pair w LeqProof) ->
           withKnownNat w $ return (Some $ mkKnownReprObj $ BVRepr w)) <|>
   (do try (string "llvmptr" >> spaces1)
       parseKnownNatRepr (return . Some . mkKnownReprObj . LLVMPointerRepr)) <|>
   (do try (string "llvmframe" >> spaces1)
       parseKnownNatRepr (return . Some . mkKnownReprObj . LLVMFrameRepr)) <|>
   (do try (string "llvmshape" >> spaces1)
       parseKnownNatRepr (return . Some . mkKnownReprObj . LLVMShapeRepr)) <|>
   (do try (string "llvmblock" >> spaces1)
       parseKnownNatRepr (return . Some . mkKnownReprObj . LLVMBlockRepr)) <|>
   (do try (string "lifetime")
       return (Some $ mkKnownReprObj LifetimeRepr)) <|>
   (do try (string "rwmodality")
       return (Some $ mkKnownReprObj RWModalityRepr)) <|>
   (do try (string "permlist")
       return (Some $ mkKnownReprObj PermListRepr)) <|>
   (do try (string "struct")
       spaces
       some_fld_tps <- parseInParens parseStructFieldTypesKnown
       case some_fld_tps of
         Some fld_tps@KnownReprObj ->
           return $ Some $ mkKnownReprObj $
           StructRepr $ unKnownReprObj fld_tps) <|>
   (do try (string "perm")
       spaces
       known_tp <- parseInParens parseTypeKnown
       case known_tp of
         Some tp@KnownReprObj ->
           return $ Some $ mkKnownReprObj $ ValuePermRepr $ unKnownReprObj tp)
   <?> "type")

-- | Parse a comma-separated list of struct field types
parseStructFieldTypesKnown :: Stream s Identity Char =>
                              PermParseM s (Some (KnownReprObj
                                                  (Assignment TypeRepr)))
parseStructFieldTypesKnown =
  helper <$> reverse <$> sepBy parseTypeKnown (spaces >> char ',')
  where
    helper :: [Some (KnownReprObj TypeRepr)] ->
              Some (KnownReprObj (Assignment TypeRepr))
    helper [] = Some $ mkKnownReprObj Ctx.empty
    helper (Some tp@KnownReprObj : tps) =
      case helper tps of
        Some repr@KnownReprObj ->
          Some $ mkKnownReprObj $
          extend (unKnownReprObj repr) (unKnownReprObj tp)


-- | Parse a Crucible type as a 'TypeRepr'
parseType :: Stream s Identity Char => PermParseM s (Some TypeRepr)
parseType = mapSome unKnownReprObj <$> parseTypeKnown


----------------------------------------------------------------------
-- * Parsing Expressions
----------------------------------------------------------------------

-- | Parse a valid identifier as a 'String'
parseIdent :: Stream s Identity Char => PermParseM s String
parseIdent =
  (do spaces
      c <- letter
      cs <- many (alphaNum <|> char '_' <|> char '\'')
      return (c:cs)) <?> "identifier"

-- | Parse a valid identifier string as an expression variable
parseExprVarAndStr :: Stream s Identity Char => PermParseM s (String, SomeName)
parseExprVarAndStr =
  do str <- parseIdent
     env <- getState
     case lookupExprVar str env of
       Just x -> return (str, x)
       Nothing -> fail ("unknown variable: " ++ str)

-- | Parse a valid identifier string as an expression variable
parseExprVar :: Stream s Identity Char => PermParseM s SomeName
parseExprVar = snd <$> parseExprVarAndStr

-- | Parse an identifier as an expression variable of a specific type
parseExprVarOfType :: Stream s Identity Char => TypeRepr a ->
                      PermParseM s (ExprVar a)
parseExprVarOfType tp =
  do some_nm <- parseExprVar
     castTypedM "variable" tp some_nm

-- | Parse a single bitvector factor of the form @x*n@, @n*x@, @x@, or @n@,
-- where @x@ is a variable and @n@ is an integer. Note that this returns a
-- 'PermExpr' and not a 'BVFactor' because the latter does not include the
-- constant integer case @n@.
parseBVFactor :: (1 <= w, KnownNat w, Stream s Identity Char) =>
                 PermParseM s (PermExpr (BVType w))
parseBVFactor =
  spaces >>
  (try (do i <- integer
           spaces >> char '*' >> spaces
           x <- parseExprVarOfType knownRepr
           return $ bvMult i (PExpr_Var x))
   <|>
   try (do x <- parseExprVarOfType knownRepr
           spaces >> char '*' >> spaces
           i <- integer
           return $ bvMult i (PExpr_Var x))
   <|>
   try (do x <- parseExprVarOfType knownRepr
           return $ PExpr_Var x)
   <|>
   do i <- integer
      return $ bvInt i)

-- | Parse a bitvector expression of the form
--
-- > f1 + ... + fn
--
-- where each @fi@ is a factor parsed by 'parseBVFactor'
parseBVExpr :: (1 <= w, KnownNat w, Stream s Identity Char) =>
               PermParseM s (PermExpr (BVType w))
parseBVExpr = parseBVExprH Proxy

-- | Helper for 'parseBVExpr'
parseBVExprH :: (1 <= w, KnownNat w, Stream s Identity Char) =>
                Proxy w -> PermParseM s (PermExpr (BVType w))
parseBVExprH w =
  (normalizeBVExpr <$> foldr1 bvAdd <$>
   sepBy1 parseBVFactor (spaces >> char '+'))
  <?> ("expression of type bv " ++ show (natVal w))

-- | Parse an 'LLVMFieldShape' of width @w@ of the form @(sz,p)@ or just @p@ if
-- @sz=w@
parseLLVMFieldShape :: (Stream s Identity Char, Liftable s, 1 <= w, KnownNat w) =>
                       f w -> PermParseM s (LLVMFieldShape w)
parseLLVMFieldShape w =
  (LLVMFieldShape <$> parseValPerm (LLVMPointerRepr $ natRepr w)) <|>
  parseInParens (do Some (Pair sz LeqProof) <- parseNatRepr
                    withKnownNat sz
                      (LLVMFieldShape <$> parseValPerm (LLVMPointerRepr sz))) <?>
  "llvm field shape"

-- | Parse an expression of a known type
parseExpr :: (Stream s Identity Char, Liftable s) => TypeRepr a ->
             PermParseM s (PermExpr a)
parseExpr UnitRepr =
  try (string "unit" >> return PExpr_Unit) <|>
  (PExpr_Var <$> parseExprVarOfType UnitRepr) <?>
  "unit expression"
parseExpr NatRepr =
  (PExpr_Nat <$> fromInteger <$> integer) <|>
  (PExpr_Var <$> parseExprVarOfType NatRepr) <?>
  "nat expression"
parseExpr (BVRepr w) = withKnownNat w parseBVExpr
parseExpr tp@(StructRepr fld_tps) =
  spaces >>
  ((string "struct" >> spaces >>
    parseInParens (PExpr_Struct <$> parseExprs (mkCruCtx fld_tps))) <|>
   (PExpr_Var <$> parseExprVarOfType tp)) <?>
  "struct expression"
parseExpr LifetimeRepr =
  try (string "always" >> return PExpr_Always) <|>
  (PExpr_Var <$> parseExprVarOfType LifetimeRepr) <?>
  "lifetime expression"
parseExpr tp@(LLVMPointerRepr w) =
  withKnownNat w $
  spaces >>
  ((do try (string "llvmword" >> spaces >> char '(')
       e <- parseExpr (BVRepr w)
       spaces >> char ')'
       return $ PExpr_LLVMWord e) <|>
   (do x <- parseExprVarOfType tp
       try (do spaces >> char '+'
               off <- parseBVExpr
               return $ PExpr_LLVMOffset x off) <|>
         return (PExpr_Var x)) <?>
   "llvmptr expression")
parseExpr tp@(FunctionHandleRepr _ _) =
  do str <- parseIdent
     env <- getState
     case lookupExprVar str env of
       Just some_x ->
         PExpr_Var <$> castTypedM "variable" tp some_x
       Nothing ->
         case lookupFunHandle (parserEnvPermEnv env) str of
           Just (SomeHandle hn)
             | Just Refl <- testEquality tp (handleType hn) ->
               return $ PExpr_Fun hn
           Just (SomeHandle hn) ->
             unexpected ("function " ++ str ++ " of type " ++
                         show (handleType hn))
           Nothing ->
             unexpected ("unknown variable or function: " ++ str)
parseExpr PermListRepr =
  -- FIXME: parse non-empty perm lists
  (string "[]" >> return PExpr_PermListNil) <|>
  (PExpr_Var <$> parseExprVarOfType PermListRepr) <?>
  "permission list expression"
parseExpr RWModalityRepr =
  (string "R" >> return PExpr_Read) <|> (string "W" >> return PExpr_Write) <|>
  (PExpr_Var <$> parseExprVarOfType knownRepr) <?>
  "rwmodality expression"
parseExpr (ValuePermRepr tp) = PExpr_ValPerm <$> parseValPerm tp
parseExpr tp@(LLVMShapeRepr w) =
  withKnownNat w $
  do spaces
     sh1 <-
       parseInParens (parseExpr tp) <|>
       (try (string "emptysh") >> return (PExpr_EmptyShape)) <|>
       (try (string "eqsh") >> spaces >> parseInParens
        (PExpr_EqShape <$> parseExpr (LLVMBlockRepr w))) <|>
       (try (string "ptrsh") >> spaces >>
        PExpr_FieldShape <$> parseLLVMFieldShape w) <|>
       (try (string "arraysh") >> spaces >> parseInParens
        (do len <- parseExpr (BVRepr w)
            spaces >> comma >> spaces
            stride <- Bytes <$> integer
            spaces >> comma >> spaces >> char '['
            flds <- sepBy1 (parseLLVMFieldShape w) (spaces >> comma)
            spaces >> char ']'
            return $ PExpr_ArrayShape len stride flds)) <|>
       (do try (string "exsh" >> spaces1)
           var <- parseIdent
           spaces >> char ':'
           some_known_tp' <- parseTypeKnown
           spaces >> char '.'
           case some_known_tp' of
             Some ktp'@KnownReprObj ->
               fmap PExpr_ExShape $ mbM $ nu $ \z ->
               withExprVar var (unKnownReprObj ktp') z $
               parseExpr tp) <|>
       (do nm <- try (do nm <- parseIdent
                         char '<' >> return nm)
           env <- parserEnvPermEnv <$> getState
           case lookupNamedShape env nm of
             Just (SomeNamedShape _ arg_ctx mb_sh)
               | Just Refl <- testEquality (mbLift $ fmap exprType mb_sh) tp ->
                 do args <- parseExprs arg_ctx
                    spaces >> char '>'
                    return (subst (substOfExprs args) mb_sh)
             Just (SomeNamedShape _ _ mb_sh) ->
               fail $ renderDoc $ sep
               [ pretty "Named shape" <+> pretty nm <+>
                 pretty "is of incorrect type"
               , pretty "Expected:" <+> permPretty emptyPPInfo tp
               , pretty "Found:" <+>
                 permPretty emptyPPInfo (mbLift $ fmap exprType mb_sh) ]
             Nothing -> unexpected ("Unknown shape name: " ++ nm)) <|>
       (PExpr_Var <$> parseExprVarOfType tp) <?>
       "llvmshape expression"
     spaces
     (try (string ";") >> spaces >> PExpr_SeqShape sh1 <$> parseExpr tp) <|>
       (try (string "orsh") >> spaces >> PExpr_OrShape sh1 <$> parseExpr tp) <|>
       return sh1
parseExpr tp = PExpr_Var <$> parseExprVarOfType tp <?> ("expression of type "
                                                        ++ show tp)

-- | Parse a comma-separated list of expressions to a 'PermExprs'
parseExprs :: (Stream s Identity Char, Liftable s) => CruCtx ctx ->
              PermParseM s (PermExprs ctx)
parseExprs CruCtxNil = return PExprs_Nil
parseExprs (CruCtxCons CruCtxNil tp) =
  -- Special case for a 1-element context: do not parse a comma
  PExprs_Cons PExprs_Nil <$> parseExpr tp
parseExprs (CruCtxCons ctx tp) =
  do es <- parseExprs ctx
     spaces >> char ','
     e <- parseExpr tp
     return $ PExprs_Cons es e


----------------------------------------------------------------------
-- * Parsing Permissions
----------------------------------------------------------------------

-- | Parse a value permission of a known type
parseValPerm :: (Stream s Identity Char, Liftable s) => TypeRepr a ->
                PermParseM s (ValuePerm a)
parseValPerm tp =
  do spaces
     p1 <-
       (parseInParens (parseValPerm tp)) <|>
       try (string "true" >> return ValPerm_True) <|>
       (do try (string "eq" >> spaces >> char '(')
           e <- parseExpr tp
           spaces >> char ')'
           return (ValPerm_Eq e)) <|>
       (do try (string "exists" >> spaces1)
           var <- parseIdent
           spaces >> char ':'
           some_known_tp' <- parseTypeKnown
           spaces >> char '.'
           case some_known_tp' of
             Some ktp'@KnownReprObj ->
               fmap ValPerm_Exists $ mbM $ nu $ \z ->
               withExprVar var (unKnownReprObj ktp') z $
               parseValPerm tp) <|>
       (do n <- try (parseIdent >>= \n -> spaces >> char '<' >> return n)
           env <- parserEnvPermEnv <$> getState
           case lookupNamedPermName env n of
             Just (SomeNamedPermName rpn)
               | Just Refl <- testEquality (namedPermNameType rpn) tp ->
                 do args <- parseExprs (namedPermNameArgs rpn)
                    spaces >> char '>'
                    off <- parsePermOffset tp
                    return $ ValPerm_Named rpn args off
             Just (SomeNamedPermName rpn) ->
               fail $ renderDoc $ sep
               [ pretty "Named permission" <+> pretty n <+>
                 pretty "is of incorrect type"
               , pretty "Expected:" <+> permPretty emptyPPInfo tp
               , pretty "Found:" <+>
                 permPretty emptyPPInfo (namedPermNameType rpn) ]
             Nothing ->
               fail ("Unknown named permission '" ++ n ++ "'")) <|>
       (ValPerm_Conj <$> parseAtomicPerms tp) <|>
       (ValPerm_Var <$> parseExprVarOfType (ValuePermRepr tp)
        <*> parsePermOffset tp) <?>
       ("permission of type " ++ show tp)
     -- FIXME: I think the SAW lexer can't handle "\/" in strings...?
     -- try (spaces >> string "\\/" >> (ValPerm_Or p1 <$> parseValPerm tp)) <|>
     (try (spaces1 >> string "or" >> space) >> (ValPerm_Or p1 <$>
                                                parseValPerm tp)) <|>
       return p1

-- | Parse a value permission of a known type in a given context
parseValPermInCtx :: (Stream s Identity Char, Liftable s) =>
                     ParsedCtx ctx -> TypeRepr a ->
                     PermParseM s (Mb ctx (ValuePerm a))
parseValPermInCtx ctx tp = inParsedCtxM ctx $ const $ parseValPerm tp

-- | Parse a @*@-separated list of atomic permissions
parseAtomicPerms :: (Stream s Identity Char, Liftable s) => TypeRepr a ->
                    PermParseM s [AtomicPerm a]
parseAtomicPerms tp =
  do p1 <- parseAtomicPerm tp
     (try (spaces >> string "*") >> (p1:) <$> parseAtomicPerms tp) <|> return [p1]

-- | Parse an atomic permission of a specific type
parseAtomicPerm :: (Stream s Identity Char, Liftable s) => TypeRepr a ->
                   PermParseM s (AtomicPerm a)
parseAtomicPerm tp@(LLVMPointerRepr w)
  | Left LeqProof <- decideLeq oneRepr w =
    withKnownNat w
    ((llvmArrayFieldToAtomicPerm <$> parseLLVMFieldPerm w False) <|>
     (Perm_LLVMArray <$> parseLLVMArrayPerm) <|>
     (do llvmBlockLifetime <-
           try (do l <- parseLifetimePrefix
                   spaces >> string "memblock" >> spaces >> char '('
                   return l)
         llvmBlockRW <- parseExpr RWModalityRepr
         spaces >> comma
         llvmBlockOffset <- parseBVExpr
         spaces >> comma
         llvmBlockLen <- parseBVExpr
         spaces >> comma
         llvmBlockShape <- parseExpr (LLVMShapeRepr w)
         spaces >> char ')'
         return (Perm_LLVMBlock $ LLVMBlockPerm {..})) <|>
     (do try (string "free" >> spaces >> char '(')
         e <- parseBVExpr
         spaces >> char ')'
         return $ Perm_LLVMFree e) <|>
     (do try (string "llvmfunptr" >> spaces >> char '{')
         Some (Pair args_no _) <- parseNatRepr
         spaces >> char ',' >> spaces
         Some (Pair w' LeqProof)  <- parseNatRepr
         spaces >> char '}' >> spaces >> char '('
         Some args <- return $ cruCtxReplicate args_no (LLVMPointerRepr w')
         SomeFunPerm fun_perm <- parseFunPermM args (LLVMPointerRepr w')
         spaces >> char ')'
         return $ mkPermLLVMFunPtr w fun_perm) <|>     
     (Perm_BVProp <$> parseBVProp) <|>
     parseAtomicNamedPerm tp <?>
     ("atomic permission of type " ++ show tp))

parseAtomicPerm tp@(LLVMFrameRepr w)
  | Left LeqProof <- decideLeq oneRepr w =
    withKnownNat w
    ((do try (string "llvmframe") >> spaces >> char '['
         fperm <-
           sepBy (do spaces
                     e <- parseExpr knownRepr
                     spaces >> char ':' >> spaces
                     i <- integer
                     return (e,i))
           (spaces >> comma)
         spaces >> char ']'
         return $ Perm_LLVMFrame fperm) <?>
     ("atomic permission of type " ++ show tp))

parseAtomicPerm tp@(LLVMBlockRepr w) =
  (do (try (string "shape") >> spaces1)
      withKnownNat w (Perm_LLVMBlockShape <$>
                      parseExpr (LLVMShapeRepr w))) <?>
  ("atomic permission of type " ++ show tp)

parseAtomicPerm tp =
  parseAtomicNamedPerm tp <?>
  ("Expecting atomic permission of type " ++ show tp)


-- | Parse a @\@e@ string as a 'PermOffset'
parsePermOffset :: (Stream s Identity Char, Liftable s) =>
                   TypeRepr a -> PermParseM s (PermOffset a)
parsePermOffset (LLVMPointerRepr w) =
  withKnownNat w
  ((do try (spaces >> char '@')
       e <- (parseBVExpr <|> parseInParens parseBVExpr)
       return $ LLVMPermOffset e)
   <|> return NoPermOffset)
parsePermOffset _ = return NoPermOffset

-- | Parse a @P<args>@ form as an LLVM named permission
parseAtomicNamedPerm :: (Stream s Identity Char, Liftable s) =>
                        TypeRepr a -> PermParseM s (AtomicPerm a)
parseAtomicNamedPerm tp =
  do n <- try (parseIdent >>= \n -> spaces >> char '<' >> return n)
     env <- parserEnvPermEnv <$> getState
     case lookupNamedPermName env n of
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) tp
         , TrueRepr <- nameIsConjRepr npn ->
             do args <- parseExprs (namedPermNameArgs npn)
                spaces >> char '>'
                off <- parsePermOffset tp
                return (Perm_NamedConj npn args off)
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) tp ->
         fail ("Non-conjoinable permission name '" ++ n
               ++ "' used in conjunctive context")
       Just (SomeNamedPermName _) ->
         fail ("Permission name '" ++ n ++ "' has incorrect type")
       Nothing ->
         fail ("Unknown permission name '" ++ n ++ "'")

-- | Parse an optional prefix of the form @[l]@ where @l@ is a lifetime, or
-- otherwise return @always@ if this prefix is missing
parseLifetimePrefix :: (Stream s Identity Char, Liftable s) =>
                       PermParseM s (PermExpr LifetimeType)
parseLifetimePrefix =
  (do try (spaces >> string "[")
      l <- parseExpr knownRepr
      spaces >> string "]"
      return l) <|> return PExpr_Always

-- | Parse a field permission @[l]ptr((rw,off) |-> p)@. If the 'Bool' flag is
-- 'True', the field permission is being parsed as part of an array permission,
-- so that @ptr@ and outer parentheses should be omitted. If the 'Bool' flag is
-- 'False', only consume input if that input starts with @( )* "ptr" ( )* "("@,
-- while if it is 'True', only consume input if it starts with @( )* "("@.
-- Return an 'LLVMArrayField', which quantifies over the size.
parseLLVMFieldPerm :: (Stream s Identity Char, Liftable s,
                       KnownNat w, 1 <= w) =>
                      NatRepr w -> Bool -> PermParseM s (LLVMArrayField w)
parseLLVMFieldPerm w in_array =
  do llvmFieldLifetime <-
       try (do l <- parseLifetimePrefix
               if in_array then spaces >> char '(' >> return ()
                 else spaces >> string "ptr" >> spaces >> char '(' >>
                      spaces >> char '(' >> return ()
               return l)
     llvmFieldRW <- parseExpr RWModalityRepr
     spaces >> comma
     llvmFieldOffset <- parseExpr (BVRepr w)
     some_sz_leq <-
       (spaces >> comma >> parseNatRepr) <|>
       (return $ Some (Pair w LeqProof))
     case some_sz_leq of
       Some (Pair sz LeqProof) ->
         withKnownNat sz $ 
         do spaces >> string ")" >> spaces >> string "|->" >> spaces
            llvmFieldContents <- parseValPerm (LLVMPointerRepr sz)
            if in_array then return () else spaces >> string ")" >> return ()
            return (LLVMArrayField $ LLVMFieldPerm {..})

-- | Parse an array permission @array(off,<len,*stride,[fp1,...])@. Only consume
-- input if that input starts with @"array" ( )* "("@.
parseLLVMArrayPerm :: (Stream s Identity Char, Liftable s,
                       KnownNat w, 1 <= w) =>
                      PermParseM s (LLVMArrayPerm w)
parseLLVMArrayPerm =
  do try (spaces >> string "array" >> spaces >> char '(')
     llvmArrayOffset <- parseBVExpr
     spaces >> comma >> spaces >> char '<'
     llvmArrayLen <- parseBVExpr
     spaces >> comma >> spaces >> char '*'
     llvmArrayStride <- Bytes <$> integer
     spaces >> comma >> spaces >> char '['
     llvmArrayFields <-
       sepBy1 (parseLLVMFieldPerm knownNat True) (spaces >> comma)
     let llvmArrayBorrows = []
     spaces >> char ']' >> spaces >> char ')'
     return LLVMArrayPerm {..}

-- | Parse a 'BVProp'
parseBVProp :: (Stream s Identity Char, Liftable s, KnownNat w, 1 <= w) =>
               PermParseM s (BVProp w)
parseBVProp =
  (try parseBVExpr >>= \e1 ->
    (do try (spaces >> string "==")
        e2 <- parseBVExpr
        return $ BVProp_Eq e1 e2) <|>
    (do try (spaces >> string "/=")
        e2 <- parseBVExpr
        return $ BVProp_Neq e1 e2) <|>
    (do try (spaces >> string "<u" >> spaces)
        e2 <- parseBVExpr
        return $ BVProp_ULt e1 e2) <|>
    (do try (spaces >> string "<=u" >> spaces)
        e2 <- parseBVExpr
        return $ BVProp_ULeq e1 e2)) <?>
  "bitvector proposition"

-- | Parse a 'BVRange' written as @{ off, len }@
parseBVRange :: (Stream s Identity Char, Liftable s, KnownNat w, 1 <= w) =>
                PermParseM s (BVRange w)
parseBVRange =
  do try (spaces >> char '{')
     bvRangeOffset <- parseBVExpr
     spaces >> comma
     bvRangeLength <- parseBVExpr
     spaces >> char '}'
     return BVRange {..}


----------------------------------------------------------------------
-- * Parsing Permission Sets and Function Permissions
----------------------------------------------------------------------

-- | A sequence of variable names and their types
data ParsedCtx ctx = ParsedCtx {
  parsedCtxNames :: RAssign (Constant String) ctx,
  parsedCtxCtx :: CruCtx ctx
  }

-- | Remove the last variable in a 'ParsedCtx'
parsedCtxUncons :: ParsedCtx (ctx :> tp) -> ParsedCtx ctx
parsedCtxUncons (ParsedCtx (xs :>: _) (CruCtxCons ctx _)) = ParsedCtx xs ctx

-- | Add a variable name and type to a 'ParsedCtx'
consParsedCtx :: String -> TypeRepr tp -> ParsedCtx ctx ->
                 ParsedCtx (ctx :> tp)
consParsedCtx x tp (ParsedCtx xs ctx) =
  ParsedCtx (xs :>: Constant x) (CruCtxCons ctx tp)

-- | A 'ParsedCtx' with a single element
singletonParsedCtx :: String -> TypeRepr tp -> ParsedCtx (RNil :> tp)
singletonParsedCtx x tp =
  ParsedCtx (MNil :>: Constant x) (CruCtxCons CruCtxNil tp)

-- | An empty 'ParsedCtx'
emptyParsedCtx :: ParsedCtx RNil
emptyParsedCtx = ParsedCtx MNil CruCtxNil

-- | Append two 'ParsedCtx's
appendParsedCtx :: ParsedCtx ctx1 -> ParsedCtx ctx2 ->
                   ParsedCtx (ctx1 :++: ctx2)
appendParsedCtx (ParsedCtx ns1 ctx1) (ParsedCtx ns2 ctx2) =
  ParsedCtx (RL.append ns1 ns2) (appendCruCtx ctx1 ctx2)

-- | Add a variable name and type to the beginning of an unknown 'ParsedCtx'
preconsSomeParsedCtx :: String -> Some TypeRepr -> Some ParsedCtx ->
                        Some ParsedCtx
preconsSomeParsedCtx x (Some (tp :: TypeRepr tp)) (Some (ParsedCtx ns tps)) =
  Some $ ParsedCtx
  (RL.append (MNil :>: (Constant x :: Constant String tp)) ns)
  (appendCruCtx (singletonCruCtx tp) tps)

-- | Make a 'ParsedCtx' where the string names are @"arg0,arg1,..."@
mkArgsParsedCtx :: CruCtx ctx -> ParsedCtx ctx
mkArgsParsedCtx ctx = ParsedCtx (helper ctx) ctx where
  helper :: CruCtx ctx' -> RAssign (Constant String) ctx'
  helper CruCtxNil = MNil
  helper (CruCtxCons ctx tp) =
    helper ctx :>: Constant ("arg" ++ show (cruCtxLen ctx))

-- | Change the type of the last element of a 'ParsedCtx'
parsedCtxSetLastType :: TypeRepr tp -> ParsedCtx (ctx :> tp') ->
                        ParsedCtx (ctx :> tp)
parsedCtxSetLastType tp (ParsedCtx (xs :>: Constant str) (CruCtxCons ctx _)) =
  (ParsedCtx (xs :>: Constant str) (CruCtxCons ctx tp))

-- | Extract out the last element of a 'ParsedCtx' as a singleton 'ParsedCtx'
parsedCtxLast :: ParsedCtx (ctx :> tp) -> ParsedCtx (RNil :> tp)
parsedCtxLast (ParsedCtx (_ :>: Constant str) (CruCtxCons _ tp)) =
  ParsedCtx (MNil :>: Constant str) (CruCtxCons CruCtxNil tp)

-- | Parse a typing context @x1:tp1, x2:tp2, ...@
parseCtx :: (Stream s Identity Char, Liftable s) =>
            PermParseM s (Some ParsedCtx)
parseCtx =
  (do x <- try parseIdent
      spaces >> char ':'
      some_tp <- parseType
      try (do spaces >> comma
              some_ctx' <- parseCtx
              return $ preconsSomeParsedCtx x some_tp some_ctx')
        <|>
        (case some_tp of
            Some tp -> return (Some $ singletonParsedCtx x tp))) <|>
  return (Some emptyParsedCtx)

-- | Parse a sequence @x1:p1, x2:p2, ...@ of variables and their permissions
--
-- FIXME: not used
parseDistPerms :: (Stream s Identity Char, Liftable s) =>
                  PermParseM s (Some DistPerms)
parseDistPerms =
  parseExprVar >>= \some_x ->
  case some_x of
    Some (Typed tp x) ->
      do p <- parseValPerm tp
         try (do spaces >> comma
                 some_dist_perms' <- parseDistPerms
                 case some_dist_perms' of
                   Some perms ->
                     return $ Some (DistPermsCons perms x p))
           <|>
           return (Some $ distPerms1 x p)

-- | Helper type for 'parseValuePerms' that represents whether a pair @x:p@ has
-- been parsed yet for a specific variable @x@ and, if so, contains that @p@
data VarPermSpec a = VarPermSpec (Name a) (Maybe (ValuePerm a))

-- | A sequence of variables @x@ and what pairs @x:p@ have been parsed so far
type VarPermSpecs = RAssign VarPermSpec

-- | Build a 'VarPermSpecs' from a list of names
mkVarPermSpecs :: RAssign Name ctx -> VarPermSpecs ctx
mkVarPermSpecs = RL.map (\n -> VarPermSpec n Nothing)

-- | Find a 'VarPermSpec' for a particular variable
findVarPermSpec :: Name (a :: CrucibleType) ->
                   VarPermSpecs ctx -> Maybe (Member ctx a)
findVarPermSpec _ MNil = Nothing
findVarPermSpec n (_ :>: VarPermSpec n' _)
  | Just Refl <- testEquality n n'
  = Just Member_Base
findVarPermSpec n (specs :>: _) = Member_Step <$> findVarPermSpec n specs

-- | Try to set the permission for a variable in a 'VarPermSpecs' list, raising
-- a parse error if the variable already has a permission or is one of the
-- expected variables
setVarSpecsPermM :: Stream s Identity Char =>
                    String -> Name tp -> ValuePerm tp -> VarPermSpecs ctx ->
                    PermParseM s (VarPermSpecs ctx)
setVarSpecsPermM _ n p var_specs
  | Just memb <- findVarPermSpec n var_specs
  , VarPermSpec _ Nothing <- RL.get memb var_specs =
    return $ RL.modify memb (const $ VarPermSpec n $ Just p) var_specs
setVarSpecsPermM var n _ var_specs
  | Just memb <- findVarPermSpec n var_specs =
    unexpected ("Variable " ++ var ++ " occurs more than once!")
setVarSpecsPermM var n _ var_specs =
    unexpected ("Unknown variable: " ++ var)

-- | Convert a 'VarPermSpecs' sequence to a sequence of permissions, using the
-- @true@ permission for any variables without permissions
varSpecsToPerms :: VarPermSpecs ctx -> ValuePerms ctx
varSpecsToPerms MNil = ValPerms_Nil
varSpecsToPerms (var_specs :>: VarPermSpec _ (Just p)) =
  ValPerms_Cons (varSpecsToPerms var_specs) p
varSpecsToPerms (var_specs :>: VarPermSpec _ Nothing) =
  ValPerms_Cons (varSpecsToPerms var_specs) ValPerm_True

-- | Parse a sequence @x1:p1, x2:p2, ...@ of variables and their permissions,
-- where each variable occurs at most once. The input list says which variables
-- can occur and which have already been seen. Return a sequence of the
-- permissions in the same order as the input list of variables.
parseSortedValuePerms :: (Stream s Identity Char, Liftable s) =>
                         VarPermSpecs ctx ->
                         PermParseM s (ValuePerms ctx)
parseSortedValuePerms var_specs =
  try (spaces >> string "empty" >> return (varSpecsToPerms var_specs)) <|>
  (parseExprVarAndStr >>= \(var, some_n) ->
   case some_n of
     Some (Typed tp n) ->
       do spaces >> char ':'
          p <- parseValPerm tp
          var_specs' <- setVarSpecsPermM var n p var_specs
          (try (spaces >> comma) >> parseSortedValuePerms var_specs') <|>
            return (varSpecsToPerms var_specs'))

-- | Run a parsing computation inside a name-binding for expressions variables
-- given by a 'ParsedCtx'. Returning the results inside a name-binding.
inParsedCtxM :: (Liftable s, NuMatching a) =>
                ParsedCtx ctx -> (RAssign Name ctx -> PermParseM s a) ->
                PermParseM s (Mb ctx a)
inParsedCtxM (ParsedCtx ids tps) f =
  mbM $ nuMulti (cruCtxProxies tps) $ \ns -> withExprVars ids tps ns (f ns)

-- | Parse a sequence @x1:p1, x2:p2, ...@ of variables and their permissions,
-- and sort the result into a 'ValuePerms' in a multi-binding that is in the
-- same order as the 'ParsedCtx' supplied on input
parseSortedMbValuePerms :: (Stream s Identity Char, Liftable s) =>
                           ParsedCtx ctx -> PermParseM s (MbValuePerms ctx)
parseSortedMbValuePerms ctx =
  inParsedCtxM ctx $ \ns ->
  parseSortedValuePerms (mkVarPermSpecs ns)

-- | Parse a function permission of the form
--
-- > (x1:tp1, ...). arg1:p1, ... -o arg1:p1', ..., argn:pn', ret:p_ret
--
-- for some arbitrary context @x1:tp1, ...@ of ghost variables
parseFunPermM :: (Stream s Identity Char, Liftable s) =>
                 CruCtx args -> TypeRepr ret ->
                 PermParseM s (SomeFunPerm args ret)
parseFunPermM args ret =
  spaces >> parseInParens parseCtx >>= \some_ghosts_ctx ->
  case some_ghosts_ctx of
    Some ghosts_ctx@(ParsedCtx _ ghosts) ->
      do spaces >> char '.'
         let args_ctx = mkArgsParsedCtx args
             ghosts_args_ctx = appendParsedCtx ghosts_ctx args_ctx
         perms_in <- parseSortedMbValuePerms ghosts_args_ctx
         spaces >> string "-o"
         perms_out <-
           parseSortedMbValuePerms (consParsedCtx "ret" ret ghosts_args_ctx)
         return $ SomeFunPerm $ FunPerm ghosts args ret perms_in perms_out


----------------------------------------------------------------------
-- * Top-level Entrypoints for Parsing Things
----------------------------------------------------------------------

-- | Parse the sort of object named by the supplied 'String', calling 'fail' if
-- there is a parsing error
runPermParseM :: (Stream s Identity t, MonadFail m) =>
                 String -> PermEnv -> PermParseM s a -> s -> m a
runPermParseM obj env m str =
  case runParser m (ParserEnv [] env) "" str of
    Left err -> Fail.fail ("Error parsing " ++ obj ++ ": " ++ show err)
    Right a -> return a

-- | Parse a permission set @x1:p1, x2:p2, ...@ for the variables in the
-- supplied context
parsePermsString :: MonadFail m => String -> PermEnv -> ParsedCtx ctx ->
                    String -> m (MbValuePerms ctx)
parsePermsString nm env ctx =
  runPermParseM nm env (parseSortedMbValuePerms ctx)

-- | Parse a permission of the given type within the given context and with
-- the given named permission variables in scope
parsePermInCtxString :: MonadFail m => String -> PermEnv -> ParsedCtx ctx ->
                        TypeRepr a -> String -> m (Mb ctx (ValuePerm a))
parsePermInCtxString nm env ctx tp =
  runPermParseM nm env (parseValPermInCtx ctx tp)

-- | Parse a sequence of atomic permissions within the given context and with
-- the given named permission variables in scope
parseAtomicPermsInCtxString :: MonadFail m => String -> PermEnv -> ParsedCtx ctx ->
                               TypeRepr a -> String -> m (Mb ctx [AtomicPerm a])
parseAtomicPermsInCtxString nm env ctx tp =
  runPermParseM nm env (inParsedCtxM ctx $ const $ parseAtomicPerms tp)

-- | Parse a 'FunPerm' named by the first 'String' from the second 'String'
parseFunPermString :: MonadFail m => String -> PermEnv -> CruCtx args ->
                      TypeRepr ret -> String -> m (SomeFunPerm args ret)
parseFunPermString nm env args ret str =
  runPermParseM nm env (parseFunPermM args ret) str

-- | Parse a type context @x1:tp1, x2:tp2, ...@ named by the first 'String' from
-- the second 'String' and return a 'ParsedCtx', which contains both the
-- variable names @xi@ and their types @tpi@
parseParsedCtxString :: MonadFail m => String -> PermEnv -> String ->
                        m (Some ParsedCtx)
parseParsedCtxString nm env str = runPermParseM nm env parseCtx str

-- | Parse a type context named by the first 'String' from the second 'String'
parseCtxString :: MonadFail m => String -> PermEnv -> String -> m (Some CruCtx)
parseCtxString nm env str =
  fmapF parsedCtxCtx <$> parseParsedCtxString nm env str

-- | Parse a type named by the first 'String' from the second 'String'
parseTypeString :: MonadFail m => String -> PermEnv -> String ->
                   m (Some TypeRepr)
parseTypeString nm env str = runPermParseM nm env parseType str

-- | Parse an expression of a given type from a 'String'
parseExprInCtxString :: MonadFail m => PermEnv -> TypeRepr a -> ParsedCtx ctx ->
                        String -> m (Mb ctx (PermExpr a))
parseExprInCtxString env tp ctx str =
  runPermParseM (permPrettyString emptyPPInfo tp) env
  (inParsedCtxM ctx $ const $ parseExpr tp) str
