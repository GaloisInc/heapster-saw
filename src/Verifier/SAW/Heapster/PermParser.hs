{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Verifier.SAW.Heapster.PermParser (
  parseFunPermString,
  parseParsedCtxString,
  parseCtxString,
  parseTypeString,
  parsePermsString,
  parseFunPermStringMaybeRust,

  parseAtomicPermsInCtxString,
  parsePermInCtxString,
  parseExprInCtxString,
  ) where

import Data.List
import GHC.TypeLits
import Data.Binding.Hobbits

import Prettyprinter hiding (comma, space)

import Data.Parameterized.Some
import Data.Parameterized.TraversableF

import Lang.Crucible.Types

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.RustTypes

import Verifier.SAW.Heapster.Lexer (lexer)
import Verifier.SAW.Heapster.Located (Pos(..), Located(..))
import Verifier.SAW.Heapster.Token (Token(TEndOfInput), describeToken)
import Verifier.SAW.Heapster.Parser (parseFunPerm, parseCtx, parseType, parseExpr, parseValuePerms)
import Verifier.SAW.Heapster.TypeChecker (Tc, TypeError(..), startTc, tcFunPerm, tcCtx, tcType, tcExpr, inParsedCtxM, tcAtomicPerms, tcValPermInCtx, tcSortedMbValuePerms)
import Verifier.SAW.Heapster.ParsedCtx

----------------------------------------------------------------------
-- * Top-level Entrypoints for Parsing Things
----------------------------------------------------------------------

runParser ::
  (MonadFail m) =>
  String                                {- ^ object name                -} ->
  PermEnv                               {- ^ permission environment     -} ->
  ([Located Token] -> Either (Located Token) p) {- ^ parser             -} ->
  (p -> Tc a)                           {- ^ checker                    -} ->
  String                                {- ^ input                      -} ->
  m a
runParser obj env parser checker str =
  case parser (lexer str) of
    Left (Located _ TEndOfInput) ->
      fail $ unlines
        [ "Error parsing " ++ obj
        , "Unexpected end of input"
        , pointEnd str
        ]
    Left (Located p t) ->
      fail $ unlines
        [ "Error parsing " ++ obj ++ " at " ++ renderPos p
        , "Unexpected " ++ describeToken t
        , point p str
        ]
    Right ast ->
      case startTc (checker ast) env of
        Left (TypeError p e) ->
          fail $ unlines
            [ "Error checking " ++ obj ++ " at " ++ renderPos p
            , e
            , point p str
            ]
        Right x -> pure x

renderPos :: Pos -> String
renderPos p = "line " ++ show (posLine p) ++ " column " ++ show (posCol p)

-- | Point to the error in the line with an error.
point :: Pos -> String -> String
point p str =
  lines str !! (posLine p - 1) ++ "\n" ++
  Data.List.replicate (posCol p - 1) ' ' ++ "^"

pointEnd :: String -> String
pointEnd "" = "<<empty input>>"
pointEnd str = end ++ "\n" ++ (' ' <$ end) ++ "^"
  where
    end = last (lines str)

-- | Parse a permission set @x1:p1, x2:p2, ...@ for the variables in the
-- supplied context
parsePermsString :: MonadFail m => String -> PermEnv -> ParsedCtx ctx ->
                    String -> m (MbValuePerms ctx)
parsePermsString nm env ctx =
  runParser nm env parseValuePerms (tcSortedMbValuePerms ctx)

-- | Parse a permission of the given type within the given context and with
-- the given named permission variables in scope
parsePermInCtxString :: MonadFail m => String -> PermEnv -> ParsedCtx ctx ->
                        TypeRepr a -> String -> m (Mb ctx (ValuePerm a))
parsePermInCtxString nm env ctx tp =
  runParser nm env parseExpr (tcValPermInCtx ctx tp)

-- | Parse a sequence of atomic permissions within the given context and with
-- the given named permission variables in scope
parseAtomicPermsInCtxString :: MonadFail m => String -> PermEnv -> ParsedCtx ctx ->
                               TypeRepr a -> String -> m (Mb ctx [AtomicPerm a])
parseAtomicPermsInCtxString nm env ctx tp =
  runParser nm env parseExpr (inParsedCtxM ctx . const . tcAtomicPerms tp)

-- | Parse a 'FunPerm' named by the first 'String' from the second 'String'
parseFunPermString :: MonadFail m => String -> PermEnv -> CruCtx args ->
                      TypeRepr ret -> String -> m (SomeFunPerm args ret)
parseFunPermString nm env args ret =
  runParser nm env parseFunPerm (tcFunPerm args ret)

-- | Parse a type context @x1:tp1, x2:tp2, ...@ named by the first 'String' from
-- the second 'String' and return a 'ParsedCtx', which contains both the
-- variable names @xi@ and their types @tpi@
parseParsedCtxString :: MonadFail m => String -> PermEnv -> String ->
                        m (Some ParsedCtx)
parseParsedCtxString nm env = runParser nm env parseCtx tcCtx

-- | Parse a type context named by the first 'String' from the second 'String'
parseCtxString :: MonadFail m => String -> PermEnv -> String -> m (Some CruCtx)
parseCtxString nm env str =
  fmapF parsedCtxCtx <$> parseParsedCtxString nm env str

-- | Parse a type named by the first 'String' from the second 'String'
parseTypeString :: MonadFail m => String -> PermEnv -> String ->
                   m (Some TypeRepr)
parseTypeString nm env = runParser nm env parseType tcType

-- | Parse an expression of a given type from a 'String'
parseExprInCtxString ::
  MonadFail m =>
  PermEnv -> TypeRepr a -> ParsedCtx ctx -> String -> m (Mb ctx (PermExpr a))
parseExprInCtxString env tp ctx =
  runParser (permPrettyString emptyPPInfo tp) env parseExpr
    (inParsedCtxM ctx . const . tcExpr tp)

-- | Parse a 'FunPerm' named by the first 'String' from the second 'String'.
-- The 'FunPerm' can either be standard Heapster syntax, which begins with an
-- open parenthesis (after optional whitespace), or it could be given in Rust
-- syntax, which begins with an angle bracket. The @w@ argument gives the bit
-- width of pointers in the current architecture.
parseFunPermStringMaybeRust :: (1 <= w, KnownNat w, MonadFail m) =>
                               String -> prx w -> PermEnv -> CruCtx args ->
                               TypeRepr ret -> String -> m (SomeFunPerm args ret)
parseFunPermStringMaybeRust nm w env args ret str =
  case find (\c -> c == '<' || c == '(') str of
    Just '<' -> parseFunPermFromRust env w args ret str
    _ -> parseFunPermString nm env args ret str
