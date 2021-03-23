module Verifier.SAW.Heapster.Token
  ( Token(..),
    tokenNat,
    tokenIdent,
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
  | TDoubleColon
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
