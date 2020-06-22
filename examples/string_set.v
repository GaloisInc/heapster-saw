
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module StringSet.

Definition listInsertM : forall (a : Type), (((@Datatypes.list) (a))) -> (a) -> ((CompM) (((@sigT) (unit) ((fun (_ : unit) => ((@Datatypes.list) (a))))))) :=
  (fun (a : Type) (l : ((@Datatypes.list) (a))) (s : a) => ((((@returnM) (CompM) (_))) (((@sigT) (unit) ((fun (_ : unit) => ((@Datatypes.list) (a)))))) (((@existT) (unit) ((fun (_ : unit) => ((@Datatypes.list) (a)))) (tt) (((@Datatypes.cons) (a) (s) (l))))))).

Definition listRemoveM : forall (a : Type), ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) -> (((@Datatypes.list) (a))) -> (a) -> ((CompM) (((@sigT) (unit) ((fun (_ : unit) => ((prod) (((@Datatypes.list) (a))) (((prod) (a) (unit))))))))) :=
  (fun (a : Type) (test_eq : (a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (l : ((@Datatypes.list) (a))) (s : a) => ((((@returnM) (CompM) (_))) (((@sigT) (unit) ((fun (_ : unit) => ((prod) (((@Datatypes.list) (a))) (((prod) (a) (unit)))))))) (((@existT) (unit) ((fun (_ : unit) => ((prod) (((@Datatypes.list) (a))) (((prod) (a) (unit)))))) (tt) (((pair) (((@Datatypes.list_rect) (a) ((fun (_ : ((@Datatypes.list) (a))) => ((@Datatypes.list) (a)))) (((@Datatypes.nil) (a))) ((fun (s' : a) (_ : ((@Datatypes.list) (a))) (rec : ((@Datatypes.list) (a))) => if ((test_eq) (s) (s')) then rec else ((@Datatypes.cons) (a) (s') (rec)))) (l))) (((pair) (s) (tt))))))))).

Definition stringList : Type :=
  ((@Datatypes.list) (((@SAWCoreScaffolding.String)))).

Definition stringListInsertM : (((@Datatypes.list) (((@SAWCoreScaffolding.String))))) -> (((@SAWCoreScaffolding.String))) -> ((CompM) (((@sigT) (unit) ((fun (_ : unit) => ((@Datatypes.list) (((@SAWCoreScaffolding.String))))))))) :=
  (fun (l : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) (s : ((@SAWCoreScaffolding.String))) => ((((@returnM) (CompM) (_))) (((@sigT) (unit) ((fun (_ : unit) => ((@Datatypes.list) (((@SAWCoreScaffolding.String)))))))) (((@existT) (unit) ((fun (_ : unit) => ((@Datatypes.list) (((@SAWCoreScaffolding.String)))))) (tt) (((@Datatypes.cons) (((@SAWCoreScaffolding.String))) (s) (l))))))).

Definition stringListRemoveM : (((@Datatypes.list) (((@SAWCoreScaffolding.String))))) -> (((@SAWCoreScaffolding.String))) -> ((CompM) (((@sigT) (unit) ((fun (_ : unit) => ((prod) (((@stringList))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))))))) :=
  (fun (l : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) (s : ((@SAWCoreScaffolding.String))) => ((((@returnM) (CompM) (_))) (((@sigT) (unit) ((fun (_ : unit) => ((prod) (((@stringList))) (((prod) (((@SAWCoreScaffolding.String))) (unit)))))))) (((@existT) (unit) ((fun (_ : unit) => ((prod) (((@stringList))) (((prod) (((@SAWCoreScaffolding.String))) (unit)))))) (tt) (((pair) (((@Datatypes.list_rect) (((@SAWCoreScaffolding.String))) ((fun (_ : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) => ((@Datatypes.list) (((@SAWCoreScaffolding.String)))))) (((@Datatypes.nil) (((@SAWCoreScaffolding.String))))) ((fun (s' : ((@SAWCoreScaffolding.String))) (_ : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) (rec : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) => if ((@SAWCoreScaffolding.equalString) (s) (s')) then rec else ((@Datatypes.cons) (((@SAWCoreScaffolding.String))) (s') (rec)))) (l))) (((pair) (s) (tt))))))))).

Definition string : Type :=
  ((@SAWCoreScaffolding.String)).

Definition string_set : Type :=
  ((@Datatypes.list) (((@SAWCoreScaffolding.String)))).

Definition string_set_insert : forall (p0 : ((@string_set))), forall (p1 : ((@string))), ((CompM) (((@sigT) (unit) ((fun (ret0 : unit) => ((@string_set))))))) :=
  ((@listInsertM) (((@SAWCoreScaffolding.String)))).

Definition string_set_remove : forall (p0 : ((@string_set))), forall (p1 : ((@string))), ((CompM) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit))))))))) :=
  ((@listRemoveM) (((@SAWCoreScaffolding.String))) (((@SAWCoreScaffolding.equalString)))).

Definition insert_remove__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm1 : ((@string))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm2 : ((@string))) => ((@CompM.LRT_Ret) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit))))))))))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm1 : ((@string))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm2 : ((@string))) => ((@CompM.LRT_Ret) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit))))))))))))))))))) (((@CompM.LRT_Nil))))) ((fun (insert_remove : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm1 : ((@string))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm2 : ((@string))) => ((@CompM.LRT_Ret) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit))))))))))))))))))))) => ((pair) ((fun (p0 : ((@string_set))) (p1 : ((@string))) (p2 : ((@string))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))))) (tt) (((((@bindM) (CompM) (_))) (((@sigT) (unit) ((fun (ret0 : unit) => ((@string_set)))))) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))))) (((@string_set_insert) (p0) (p1))) ((fun (call_ret_val : ((@sigT) (unit) ((fun (ret0 : unit) => ((@string_set)))))) => ((((@bindM) (CompM) (_))) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))))) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))))) (((@string_set_remove) (((@projT2) (unit) ((fun (elim_call_ret_val0 : unit) => ((@string_set)))) (call_ret_val))) (p2))) ((fun (call_ret_val : ((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))))) => ((((@returnM) (CompM) (_))) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))))) (((@existT) (unit) ((fun (r0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))) (tt) (((pair) (((SAWCoreScaffolding.fst) (((@projT2) (unit) ((fun (elim_call_ret_val0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))) (call_ret_val))))) (((pair) (((SAWCoreScaffolding.fst) (((SAWCoreScaffolding.snd) (((@projT2) (unit) ((fun (elim_call_ret_val0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))) (call_ret_val))))))) (tt)))))))))))))))))) (tt))))).

Definition insert_remove : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm1 : ((@string))) => ((@CompM.LRT_Fun) (((@string))) ((fun (perm2 : ((@string))) => ((@CompM.LRT_Ret) (((@sigT) (unit) ((fun (ret0 : unit) => ((prod) (((@string_set))) (((prod) (((@string))) (unit)))))))))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@insert_remove__tuple_fun)))).

End StringSet.
