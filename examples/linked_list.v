
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module linked_list.

Definition mallocSpec : forall (sz : ((@SAWCorePrelude.bitvector) (64))), ((CompM) (((@SAWCorePrelude.BVVec) (64) (sz) (unit)))) :=
  (fun (sz : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => ((((@returnM) (CompM) (_))) (((@SAWCorePrelude.BVVec) (64) (sz) (unit))) (((@SAWCorePrelude.genBVVec) (64) (sz) (unit) ((fun (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) (_ : ((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (i) (sz))) (((@SAWCoreScaffolding.true))))) => tt)))))).

Definition is_elem__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil))))) ((fun (is_elem : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))) => ((pair) ((fun (e0 : ((@SAWCorePrelude.bitvector) (64))) (p0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (tt) (((@SAWCorePrelude.either) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (x_left0 : unit) => ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((bvLit) (64) (0%Z))) (tt)))))) ((fun (x_right0 : ((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) => if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (1) (if ((@SAWCorePrelude.bvEq) (64) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((SAWCoreScaffolding.fst) (x_right0))))) (e0)) then ((bvLit) (1) (1%Z)) else ((bvLit) (1) (0%Z))) (((bvLit) (1) (0%Z)))))) then ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((bvLit) (64) (1%Z))) (tt)))) else ((((@bindM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((is_elem) (e0) (((SAWCoreScaffolding.fst) (((SAWCoreScaffolding.snd) (x_right0))))))) ((fun (call_ret_val : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (call_ret_val))) (tt))))))))) (((@SAWCorePrelude.unfoldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p0)))))))) (tt))))).

Definition is_elem : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@is_elem__tuple_fun)))).

Definition any__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm1 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm1 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil))))) ((fun (any : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm1 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))) => ((pair) ((fun (p0 : forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (p1 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (tt) (((@SAWCorePrelude.either) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (x_left0 : unit) => ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((bvLit) (64) (0%Z))) (tt)))))) ((fun (x_right0 : ((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) => ((((@bindM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((p0) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((SAWCoreScaffolding.fst) (x_right0))))) (tt))))) ((fun (call_ret_val : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (1) (if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (64) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (call_ret_val))) (((bvLit) (64) (0%Z)))))) then ((bvLit) (1) (1%Z)) else ((bvLit) (1) (0%Z))) (((bvLit) (1) (0%Z)))))) then ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((bvLit) (64) (1%Z))) (tt)))) else ((((@bindM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((any) (p0) (((SAWCoreScaffolding.fst) (((SAWCoreScaffolding.snd) (x_right0))))))) ((fun (call_ret_val_0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (call_ret_val_0))) (tt)))))))))))) (((@SAWCorePrelude.unfoldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p1)))))))) (tt))))).

Definition any : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : forall (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))), ((CompM) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm1 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@any__tuple_fun)))).

Definition sorted_insert__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))) (((@CompM.LRT_Nil))))) ((fun (sorted_insert : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))))) => ((pair) ((fun (e0 : ((@SAWCorePrelude.bitvector) (64))) (p0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (tt) (((@SAWCorePrelude.either) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) ((fun (x_left0 : unit) => ((((@bindM) (CompM) (_))) (((@SAWCorePrelude.BVVec) (64) (((bvLit) (64) (2%Z))) (unit))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@mallocSpec) (((bvLit) (64) (2%Z))))) ((fun (call_ret_val : ((@SAWCorePrelude.BVVec) (64) (((bvLit) (64) (2%Z))) (unit))) => ((@SAWCorePrelude.maybe) (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (0%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) (((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) (((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (("0 <u 2")%string))) ((fun (ult_pf0 : ((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (0%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) => ((@SAWCorePrelude.maybe) (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) (((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) (((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (("1 <u 2")%string))) ((fun (ult_pf0_0 : ((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) => if ((@SAWCorePrelude.bvEq) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (0%Z)))) then ((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (("1 /= 0")%string)) else (((fun (catchpoint : forall (msg : ((@SAWCoreScaffolding.String))), ((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) => ((((@returnM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@SAWCorePrelude.foldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@SAWCorePrelude.Right) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (((pair) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (e0) (tt))) (((pair) (((@SAWCorePrelude.foldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@SAWCorePrelude.Left) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (tt))))) (tt)))))))))))) ((fun (msg : ((@SAWCoreScaffolding.String))) => ((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@SAWCoreScaffolding.appendString) (msg) (("
  
  --------------------
  
  at linked_list.c:58:1 (return $1):
  proveVarImplH: Could not prove
  z17:eq(LLVMword 0)
  -o
  (). ptr((W,0) |-> exists z18. eq(LLVMword z18))
      *ptr((W,8) |-> List<exists z18. eq(LLVMword z18),always,W>)
  
  --------------------
  
  at linked_list.c:58:1 (return $1):
  proveVarEqH: Could not prove
  ghost7:array(0, <2, *8, [(W,0) |-> true], [(1).0,(0).0])
         *ptr((W,0) |-> eq(ghost8))
         *ptr((W,8) |-> eq(LLVMword 0))
  -o
  (). eq(LLVMword 0)")%string))))))))) (((@SAWCorePrelude.bvultWithProof) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (2%Z)))))))) (((@SAWCorePrelude.bvultWithProof) (64) (((bvLit) (64) (0%Z))) (((bvLit) (64) (2%Z))))))))))) ((fun (x_right0 : ((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) => if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (1) (if ((@SAWCoreVectorsAsCoqVectors.bvsle) (64) (e0) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((SAWCoreScaffolding.fst) (x_right0)))))) then ((bvLit) (1) (1%Z)) else ((bvLit) (1) (0%Z))) (((bvLit) (1) (0%Z)))))) then ((((@bindM) (CompM) (_))) (((@SAWCorePrelude.BVVec) (64) (((bvLit) (64) (2%Z))) (unit))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@mallocSpec) (((bvLit) (64) (2%Z))))) ((fun (call_ret_val : ((@SAWCorePrelude.BVVec) (64) (((bvLit) (64) (2%Z))) (unit))) => ((@SAWCorePrelude.maybe) (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (0%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) (((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) (((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (("0 <u 2")%string))) ((fun (ult_pf0 : ((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (0%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) => ((@SAWCorePrelude.maybe) (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) (((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) (((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (("1 <u 2")%string))) ((fun (ult_pf0_0 : ((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (2%Z))))) (((@SAWCoreScaffolding.true))))) => if ((@SAWCorePrelude.bvEq) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (0%Z)))) then ((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (("1 /= 0")%string)) else (((fun (catchpoint : forall (msg : ((@SAWCoreScaffolding.String))), ((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) => ((((@returnM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@SAWCorePrelude.foldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@SAWCorePrelude.Right) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (((pair) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (e0) (tt))) (((pair) (((@SAWCorePrelude.foldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@SAWCorePrelude.Right) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (((pair) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((SAWCoreScaffolding.fst) (x_right0))))) (tt))) (((pair) (((SAWCoreScaffolding.fst) (((SAWCoreScaffolding.snd) (x_right0))))) (tt))))))))) (tt)))))))))))) ((fun (msg : ((@SAWCoreScaffolding.String))) => ((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@SAWCoreScaffolding.appendString) (msg) (("
  
  --------------------
  
  at linked_list.c:58:1 (return $1):
  proveVarEqH: Could not prove
  top3:ptr((W,8) |-> List<exists z19. eq(LLVMword z19),always,W>)
       *ptr((W,0) |-> eq(ghost6))
  -o
  (). eq(LLVMword 0)
  
  --------------------
  
  at linked_list.c:58:1 (return $1):
  proveVarEqH: Could not prove
  ghost9:array(0, <2, *8, [(W,0) |-> true], [(1).0,(0).0])
         *ptr((W,0) |-> eq(ghost10))
         *ptr((W,8) |-> eq(ghost11))
  -o
  (). eq(LLVMword 0)")%string))))))))) (((@SAWCorePrelude.bvultWithProof) (64) (((bvLit) (64) (1%Z))) (((bvLit) (64) (2%Z)))))))) (((@SAWCorePrelude.bvultWithProof) (64) (((bvLit) (64) (0%Z))) (((bvLit) (64) (2%Z))))))))) else ((((@bindM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((sorted_insert) (e0) (((SAWCoreScaffolding.fst) (((SAWCoreScaffolding.snd) (x_right0))))))) ((fun (call_ret_val : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => (((fun (catchpoint : forall (msg : ((@SAWCoreScaffolding.String))), ((CompM) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))) => ((((@returnM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@SAWCorePrelude.foldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@SAWCorePrelude.Right) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (unit))))) (((pair) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((SAWCoreScaffolding.fst) (x_right0))))) (tt))) (((pair) (call_ret_val) (tt)))))))))))) ((fun (msg : ((@SAWCoreScaffolding.String))) => ((((@errorM) (CompM) (_))) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) (((@SAWCoreScaffolding.appendString) (msg) (("
  
  --------------------
  
  at linked_list.c:58:1 (return $1):
  proveVarEqH: Could not prove
  top3:ptr((W,0) |-> eq(ghost6))*ptr((W,8) |-> eq(ghost8))
  -o
  (). eq(LLVMword 0)")%string)))))))))))) (((@SAWCorePrelude.unfoldList) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p0)))))))) (tt))))).

Definition sorted_insert : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) ((fun (perm0 : ((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))) => ((@CompM.LRT_Ret) (((@SAWCorePrelude.List_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@sorted_insert__tuple_fun)))).

End linked_list.
