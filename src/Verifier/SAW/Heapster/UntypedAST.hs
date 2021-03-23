module Verifier.SAW.Heapster.UntypedAST where

import GHC.Natural

import Verifier.SAW.Heapster.Located

data FunPerm = FunPerm Pos [(String, AstType)] [(String, AstExpr)] [(String, AstExpr)]
  deriving Show

data ArrayPerm = ArrayPerm Pos (Maybe AstExpr) AstExpr AstExpr (Maybe AstExpr)
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
  | ExVar Pos String [AstExpr] (Maybe AstExpr)
  | ExAdd Pos AstExpr AstExpr
  | ExMul Pos AstExpr AstExpr
  | ExRead Pos
  | ExWrite Pos
  | ExStruct Pos [AstExpr]
  | ExLlvmWord Pos AstExpr
  | ExPermList Pos [AstPerm]

  | ExEmptySh Pos
  | ExEqSh Pos AstExpr
  | ExEq Pos AstExpr
  | ExOr Pos AstExpr AstExpr
  | ExTrue Pos
  | ExExists Pos String AstType AstExpr
  | ExSeqSh Pos AstExpr AstExpr
  | ExOrSh Pos AstExpr AstExpr
  | ExExSh Pos String AstType AstExpr
  | ExFieldSh Pos AstExpr AstExpr
  | ExPtrSh Pos (Maybe AstExpr) AstExpr (Maybe AstExpr)

  | ExEqual Pos AstExpr AstExpr
  | ExNotEqual Pos AstExpr AstExpr
  | ExLessThan Pos AstExpr AstExpr
  | ExLessEqual Pos AstExpr AstExpr

  | ExLOwned Pos [(String, AstExpr)] [(String, AstExpr)]
  | ExLCurrent Pos
  | ExShape Pos AstExpr
  | ExFree Pos AstExpr
  | ExPtr Pos (Maybe AstExpr) AstExpr AstExpr (Maybe AstExpr) AstExpr
  | ExMemblock Pos (Maybe AstExpr) AstExpr AstExpr AstExpr AstExpr
  | ExLlvmFunPtr Pos AstExpr AstExpr FunPerm
  | ExArray Pos AstExpr AstExpr AstExpr [ArrayPerm]
  | ExArraySh Pos AstExpr AstExpr [(Maybe AstExpr, AstExpr)]
  deriving Show

data AstPerm = AstPerm
  deriving Show

