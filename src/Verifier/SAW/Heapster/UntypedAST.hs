module Verifier.SAW.Heapster.UntypedAST where

import GHC.Natural

import Verifier.SAW.Heapster.Located

data FunPerm = FunPerm Pos [(String, AstType)] [(String, AstExpr)] [(String, AstExpr)]
  deriving Show

data ArrayPerm = ArrayPerm Pos (Maybe AstExpr) AstExpr AstExpr (Maybe AstExpr) AstExpr
  deriving Show

data AstType
  = TyUnit Pos
  | TyBool Pos
  | TyNat Pos
  | TyBV Pos Natural
  | TyLlvmPtr Pos Natural
  | TyLlvmFrame Pos Natural
  | TyLlvmBlock Pos Natural
  | TyLlvmShape Pos Natural
  | TyLifetime Pos
  | TyRwModality Pos
  | TyPermList Pos
  | TyStruct Pos [AstType]
  | TyPerm Pos AstType
  deriving Show

data AstExpr
  = ExUnit Pos
  | ExAlways Pos
  | ExNat Pos Natural
  | ExVar Pos String (Maybe [AstExpr]) (Maybe AstExpr)
  | ExAdd Pos AstExpr AstExpr
  | ExMul Pos AstExpr AstExpr
  | ExRead Pos
  | ExWrite Pos
  | ExStruct Pos [AstExpr]
  | ExLlvmWord Pos AstExpr

  | ExEmptySh Pos
  | ExEqSh Pos AstExpr
  | ExEq Pos AstExpr
  | ExOr Pos AstExpr AstExpr
  | ExTrue Pos
  | ExExists Pos String AstType AstExpr
  | ExSeqSh Pos AstExpr AstExpr
  | ExOrSh Pos AstExpr AstExpr
  | ExExSh Pos String AstType AstExpr
  | ExFieldSh Pos (Maybe AstExpr) AstExpr
  | ExPtrSh Pos (Maybe AstExpr) (Maybe AstExpr) AstExpr

  | ExEqual Pos AstExpr AstExpr
  | ExNotEqual Pos AstExpr AstExpr
  | ExLessThan Pos AstExpr AstExpr
  | ExLessEqual Pos AstExpr AstExpr

  | ExLOwned Pos [(String, AstExpr)] [(String, AstExpr)]
  | ExLCurrent Pos (Maybe AstExpr)
  | ExShape Pos AstExpr
  | ExFree Pos AstExpr
  | ExPtr Pos (Maybe AstExpr) AstExpr AstExpr (Maybe AstExpr) AstExpr
  | ExMemblock Pos (Maybe AstExpr) AstExpr AstExpr AstExpr AstExpr
  | ExLlvmFunPtr Pos AstExpr AstExpr FunPerm
  | ExLlvmFrame Pos [(AstExpr, Natural)]
  | ExArray Pos AstExpr AstExpr AstExpr [ArrayPerm]
  | ExArraySh Pos AstExpr AstExpr [(Maybe AstExpr, AstExpr)]
  deriving Show

instance HasPos AstExpr
