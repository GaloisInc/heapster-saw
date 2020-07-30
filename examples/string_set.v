
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module StringSet.

Definition listInsertM : forall (a : Type), (((@Datatypes.list) (a))) -> (a) -> ((CompM) (((@Datatypes.list) (a)))) :=
  (fun (a : Type) (l : ((@Datatypes.list) (a))) (s : a) => ((((@returnM) (CompM) (_))) (((@Datatypes.list) (a))) (((@Datatypes.cons) (a) (s) (l))))).

Definition listRemoveM : forall (a : Type), ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) -> (((@Datatypes.list) (a))) -> (a) -> ((CompM) (((prod) (((@Datatypes.list) (a))) (((prod) (a) (unit)))))) :=
  (fun (a : Type) (test_eq : (a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (l : ((@Datatypes.list) (a))) (s : a) => ((((@returnM) (CompM) (_))) (((prod) (((@Datatypes.list) (a))) (((prod) (a) (unit))))) (((pair) (((@Datatypes.list_rect) (a) ((fun (_ : ((@Datatypes.list) (a))) => ((@Datatypes.list) (a)))) (((@Datatypes.nil) (a))) ((fun (s' : a) (_ : ((@Datatypes.list) (a))) (rec : ((@Datatypes.list) (a))) => if ((test_eq) (s) (s')) then rec else ((@Datatypes.cons) (a) (s') (rec)))) (l))) (((pair) (s) (tt))))))).

Definition stringList : Type :=
  ((@Datatypes.list) (((@SAWCoreScaffolding.String)))).

Definition stringListInsertM : (((@Datatypes.list) (((@SAWCoreScaffolding.String))))) -> (((@SAWCoreScaffolding.String))) -> ((CompM) (((@Datatypes.list) (((@SAWCoreScaffolding.String)))))) :=
  (fun (l : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) (s : ((@SAWCoreScaffolding.String))) => ((((@returnM) (CompM) (_))) (((@Datatypes.list) (((@SAWCoreScaffolding.String))))) (((@Datatypes.cons) (((@SAWCoreScaffolding.String))) (s) (l))))).

Definition stringListRemoveM : (((@Datatypes.list) (((@SAWCoreScaffolding.String))))) -> (((@SAWCoreScaffolding.String))) -> ((CompM) (((prod) (((@stringList))) (((prod) (((@SAWCoreScaffolding.String))) (unit)))))) :=
  (fun (l : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) (s : ((@SAWCoreScaffolding.String))) => ((((@returnM) (CompM) (_))) (((prod) (((@stringList))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))) (((pair) (((@Datatypes.list_rect) (((@SAWCoreScaffolding.String))) ((fun (_ : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) => ((@Datatypes.list) (((@SAWCoreScaffolding.String)))))) (((@Datatypes.nil) (((@SAWCoreScaffolding.String))))) ((fun (s' : ((@SAWCoreScaffolding.String))) (_ : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) (rec : ((@Datatypes.list) (((@SAWCoreScaffolding.String))))) => if ((@SAWCoreScaffolding.equalString) (s) (s')) then rec else ((@Datatypes.cons) (((@SAWCoreScaffolding.String))) (s') (rec)))) (l))) (((pair) (s) (tt))))))).

Definition string_set : Type :=
  ((@Datatypes.list) (((@SAWCoreScaffolding.String)))).

Definition string_set_insert : forall (p0 : ((@string_set))), forall (p1 : ((@SAWCoreScaffolding.String))), ((CompM) (((@string_set)))) :=
  ((@listInsertM) (((@SAWCoreScaffolding.String)))).

Definition string_set_remove : forall (p0 : ((@string_set))), forall (p1 : ((@SAWCoreScaffolding.String))), ((CompM) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit)))))) :=
  ((@listRemoveM) (((@SAWCoreScaffolding.String))) (((@SAWCoreScaffolding.equalString)))).

Definition insert_remove__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm1 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm2 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Ret) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit)))))))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm1 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm2 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Ret) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit)))))))))))))))) (((@CompM.LRT_Nil))))) ((fun (insert_remove : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm1 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm2 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Ret) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit)))))))))))))))))) => ((pair) ((fun (p0 : ((@string_set))) (p1 : ((@SAWCoreScaffolding.String))) (p2 : ((@SAWCoreScaffolding.String))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))) (tt) (((((@bindM) (CompM) (_))) (((@string_set))) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))) (((@string_set_insert) (p0) (p1))) ((fun (call_ret_val : ((@string_set))) => ((((@bindM) (CompM) (_))) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))) (((@string_set_remove) (call_ret_val) (p2))) ((fun (call_ret_val : ((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))) => ((((@returnM) (CompM) (_))) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))) (((pair) (((SAWCoreScaffolding.fst) (call_ret_val))) (((pair) (p2) (tt)))))))))))))))) (tt))))).

Definition insert_remove : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@string_set))) ((fun (perm0 : ((@string_set))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm1 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Fun) (((@SAWCoreScaffolding.String))) ((fun (perm2 : ((@SAWCoreScaffolding.String))) => ((@CompM.LRT_Ret) (((prod) (((@string_set))) (((prod) (((@SAWCoreScaffolding.String))) (unit))))))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@insert_remove__tuple_fun)))).

End StringSet.
