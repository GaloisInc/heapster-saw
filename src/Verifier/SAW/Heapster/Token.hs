module Verifier.SAW.Heapster.Token
  ( Token(..),
    tokenNat,
    tokenIdent,
    describeToken,
  ) where

import GHC.Natural

data Token
  = TOpenParen
  | TCloseParen
  | TOpenBrack
  | TCloseBrack
  | TOpenBrace
  | TCloseBrace
  | TOpenAngle
  | TCloseAngle
  | TColon
  | TSemicolon
  | TDot
  | TComma
  | TPlus
  | TStar
  | TAt
  | TLoli
  | TMapsTo
  | TEqual
  | TNotEqual
  | TUnsignedLt
  | TUnsignedLe
  | TOr
  | TTrue
  | TEmpty
  | TExists
  | TEq
  | TUnit
  | TBool
  | TNat
  | TBV
  | TArray
  | TPtr
  | TPerm
  | TLlvmPtr
  | TLlvmFunPtr
  | TLlvmFrame
  | TLlvmShape
  | TLlvmBlock
  | TLlvmWord
  | TLifetime
  | TLOwned
  | TLCurrent
  | TRWModality
  | TPermList
  | TStruct
  | TShape
  | TEmptySh
  | TEqSh
  | TPtrSh
  | TFieldSh
  | TArraySh
  | TExSh
  | TOrSh
  | TMemBlock
  | TFree
  | TAlways
  | TR
  | TW
  | TIdent String
  | TNatLit Natural
  | TError String
  deriving Show

tokenNat :: Token -> Maybe Natural
tokenNat (TNatLit n) = Just n
tokenNat _           = Nothing

tokenIdent :: Token -> Maybe String
tokenIdent (TIdent n) = Just n
tokenIdent _          = Nothing

describeToken :: Token -> String
describeToken t =
  case t of
    TOpenParen          -> "'('"
    TCloseParen         -> "')'"
    TOpenBrack          -> "'['"
    TCloseBrack         -> "']'"
    TOpenBrace          -> "'{'"
    TCloseBrace         -> "'}'"
    TOpenAngle          -> "'<'"
    TCloseAngle         -> "'>'"
    TColon              -> "':'"
    TDot                -> "'.'"
    TComma              -> "','"
    TSemicolon          -> "';'"
    TPlus               -> "'+'"
    TStar               -> "'*'"
    TAt                 -> "'@'"
    TLoli               -> "'-o'"
    TMapsTo             -> "'|->'"
    TEqual              -> "'=='"
    TNotEqual           -> "'/='"
    TUnsignedLt         -> "'<u'"
    TUnsignedLe         -> "'<=u'"
    TOr                 -> "keyword 'or'"
    TTrue               -> "keyword 'true'"
    TEmpty              -> "keyword 'empty'"
    TExists             -> "keyword 'exists'"
    TEq                 -> "keyword 'eq'"
    TUnit               -> "keyword 'unit'"
    TBool               -> "keyword 'bool'"
    TNat                -> "keyword 'nat'"
    TBV                 -> "keyword 'bv'"
    TArray              -> "keyword 'array'"
    TPtr                -> "keyword 'ptr'"
    TPerm               -> "keyword 'perm'"
    TLlvmPtr            -> "keyword 'llvmptr'"
    TLlvmFunPtr         -> "keyword 'llvmfunptr'"
    TLlvmFrame          -> "keyword 'llvmframe'"
    TLlvmShape          -> "keyword 'llvmshape'"
    TLlvmBlock          -> "keyword 'llvmblock'"
    TLlvmWord           -> "keyword 'llvmword'"
    TLifetime           -> "keyword 'lifetime'"
    TLOwned             -> "keyword 'lowned'"
    TLCurrent           -> "keyword 'lcurrent'"
    TRWModality         -> "keyword 'rwmodality'"
    TPermList           -> "keyword 'permlist'"
    TStruct             -> "keyword 'struct'"
    TShape              -> "keyword 'shape'"
    TEmptySh            -> "keyword 'emptysh'"
    TEqSh               -> "keyword 'eqsh'"
    TPtrSh              -> "keyword 'ptrsh'"
    TFieldSh            -> "keyword 'fieldsh'"
    TArraySh            -> "keyword 'arraysh'"
    TExSh               -> "keyword 'exsh'"
    TOrSh               -> "keyword 'orsh'"
    TMemBlock           -> "keyword 'memblock'"
    TFree               -> "keyword 'free'"
    TAlways             -> "keyword 'always'"
    TR                  -> "keyword 'R'"
    TW                  -> "keyword 'W'"
    TIdent  ident       -> "identifier " ++ ident
    TNatLit n           -> "literal " ++ show n
    TError  _           -> "lexical error"
