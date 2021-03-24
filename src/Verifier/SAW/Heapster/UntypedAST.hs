module Verifier.SAW.Heapster.UntypedAST where

import GHC.Natural

import Verifier.SAW.Heapster.Located

data AstFunPerm = AstFunPerm
  Pos
  [(Located String, AstType)]
  [(Located String, AstExpr)]
  [(Located String, AstExpr)]
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

  | ExLOwned Pos [(Located String, AstExpr)] [(Located String, AstExpr)]
  | ExLCurrent Pos (Maybe AstExpr)
  | ExShape Pos AstExpr
  | ExFree Pos AstExpr
  | ExPtr Pos (Maybe AstExpr) AstExpr AstExpr (Maybe AstExpr) AstExpr
  | ExMemblock Pos (Maybe AstExpr) AstExpr AstExpr AstExpr AstExpr
  | ExLlvmFunPtr Pos AstExpr AstExpr AstFunPerm
  | ExLlvmFrame Pos [(AstExpr, Natural)]
  | ExArray Pos AstExpr AstExpr AstExpr [ArrayPerm]
  | ExArraySh Pos AstExpr AstExpr [(Maybe AstExpr, AstExpr)]
  deriving Show

instance HasPos AstExpr where
  pos (ExUnit p) = p
  pos (ExAlways p) = p
  pos (ExNat p _) = p
  pos (ExVar p _ _ _) = p
  pos (ExAdd p _ _) = p
  pos (ExMul p _ _) = p
  pos (ExRead p) = p
  pos (ExWrite p) = p
  pos (ExStruct p _) = p
  pos (ExLlvmWord p _) = p
  pos (ExEmptySh p) = p
  pos (ExEqSh p _) = p
  pos (ExEq p _) = p
  pos (ExOr p _ _) = p
  pos (ExTrue p) = p
  pos (ExExists p _ _ _) = p
  pos (ExSeqSh p _ _) = p
  pos (ExOrSh p _ _) = p
  pos (ExExSh p _ _ _) = p
  pos (ExFieldSh p _ _) = p
  pos (ExPtrSh p _ _ _) = p
  pos (ExEqual p _ _) = p
  pos (ExNotEqual p _ _) = p
  pos (ExLessThan p _ _) = p
  pos (ExLessEqual p _ _) = p
  pos (ExLOwned p _ _) = p
  pos (ExLCurrent p _) = p
  pos (ExShape p _) = p
  pos (ExFree p _) = p
  pos (ExPtr p _ _ _ _ _) = p
  pos (ExMemblock p _ _ _ _ _) = p
  pos (ExLlvmFunPtr p _ _ _) = p
  pos (ExLlvmFrame p _) = p
  pos (ExArray p _ _ _ _) = p
  pos (ExArraySh p _ _ _) = p
