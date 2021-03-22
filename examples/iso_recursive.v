
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module iso_recursive.

Definition ListIRTTyVars : forall (a : Type), @SAWCorePrelude.ListSort :=
  fun (a : Type) => @SAWCorePrelude.LS_Cons a (@SAWCorePrelude.LS_Nil).

Definition ListIRTDesc : forall (a : Type), @SAWCorePrelude.IRTDesc (@ListIRTTyVars a) :=
  fun (a : Type) => @SAWCorePrelude.IRT_mu (@ListIRTTyVars a) (@SAWCorePrelude.IRT_Either (@ListIRTTyVars a) (@SAWCorePrelude.IRT_unit (@ListIRTTyVars a)) (@SAWCorePrelude.IRT_prod (@ListIRTTyVars a) (@SAWCorePrelude.IRT_varT (@ListIRTTyVars a) 0) (@SAWCorePrelude.IRT_prod (@ListIRTTyVars a) (@SAWCorePrelude.IRT_varD (@ListIRTTyVars a) 0) (@SAWCorePrelude.IRT_unit (@ListIRTTyVars a))))).

Definition ListIRT : forall (a : Type), Type :=
  fun (a : Type) => @SAWCorePrelude.IRT (@ListIRTTyVars a) (@SAWCorePrelude.IRTs_Nil (@ListIRTTyVars a)) (@ListIRTDesc a).

Definition unfoldListIRT : forall (a : Type), @ListIRT a -> @SAWCorePrelude.Either unit (prod a (prod (@ListIRT a) unit)) :=
  fun (a : Type) => @SAWCorePrelude.unfoldIRT (@ListIRTTyVars a) (@SAWCorePrelude.IRTs_Nil (@ListIRTTyVars a)) (@ListIRTDesc a).

Definition foldListIRT : forall (a : Type), @SAWCorePrelude.Either unit (prod a (prod (@ListIRT a) unit)) -> @ListIRT a :=
  fun (a : Type) => @SAWCorePrelude.foldIRT (@ListIRTTyVars a) (@SAWCorePrelude.IRTs_Nil (@ListIRTTyVars a)) (@ListIRTDesc a).

Definition is_elem__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.bitvector 64) (fun (arg0 : @SAWCorePrelude.bitvector 64) => @CompM.LRT_Fun (@ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (fun (perm0 : @ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.bitvector 64) (fun (arg0 : @SAWCorePrelude.bitvector 64) => @CompM.LRT_Fun (@ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (fun (perm0 : @ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))))) (@CompM.LRT_Nil)) (fun (is_elem : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.bitvector 64) (fun (arg0 : @SAWCorePrelude.bitvector 64) => @CompM.LRT_Fun (@ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (fun (perm0 : @ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))))) => pair (fun (e0 : @SAWCorePrelude.bitvector 64) (p0 : @ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) tt (@SAWCorePrelude.either unit (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) unit)) (CompM (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (fun (x_left0 : unit) => @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 0%Z) tt)) (fun (x_right0 : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) unit)) => if @SAWCoreScaffolding.not (@SAWCorePrelude.bvEq 1 (if @SAWCorePrelude.bvEq 64 (@projT1 (@SAWCorePrelude.bitvector 64) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 64) => unit) (SAWCoreScaffolding.fst x_right0)) e0 then intToBv 1 (-1)%Z else intToBv 1 0%Z) (intToBv 1 0%Z)) then @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 1%Z) tt) else @bindM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (is_elem e0 (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd x_right0))) (fun (call_ret_val : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (@projT1 (@SAWCorePrelude.bitvector 64) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 64) => unit) call_ret_val) tt))) (@unfoldListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) p0))) tt).

Definition is_elem : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.bitvector 64) (fun (arg0 : @SAWCorePrelude.bitvector 64) => @CompM.LRT_Fun (@ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (fun (perm0 : @ListIRT (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))))) :=
  SAWCoreScaffolding.fst is_elem__tuple_fun.

End iso_recursive.
