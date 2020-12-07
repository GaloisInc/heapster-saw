
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module loops.

Definition add_loop__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil))))) ((fun (add_loop : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))) => ((pair) ((fun (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.letRecM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p3 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p4 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p5 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))))))) (((@CompM.LRT_Nil))))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (f : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p3 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p4 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p5 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))))))))) => ((pair) ((fun (p2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p3 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p4 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p5 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (1) (if ((@SAWCoreVectorsAsCoqVectors.bvult) (64) (((intToBv) (64) (0%Z))) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (p5)))) then ((intToBv) (1) ((-1)%Z)) else ((intToBv) (1) (0%Z))) (((intToBv) (1) (0%Z)))))) then ((f) (p2) (p3) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (64) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (p4))) (((intToBv) (64) (1%Z))))) (tt))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (64) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (p5))) (((intToBv) (64) ((-1)%Z))))) (tt)))) else ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p4)))) (tt)))) ((fun (f : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p3 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p4 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (p5 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))))))))) => ((f) (p0) (p1) (p0) (p1))))))) (tt))))).

Definition add_loop : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@add_loop__tuple_fun)))).

Definition sign_of_sum__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))) (((@CompM.LRT_Nil))))) ((fun (sign_of_sum : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))) => ((pair) ((fun (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (tt) (((((@bindM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@add_loop) (p0) (p1))) ((fun (call_ret_val : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (1) (if ((@SAWCoreVectorsAsCoqVectors.bvslt) (64) (((intToBv) (64) (0%Z))) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (call_ret_val)))) then ((intToBv) (1) ((-1)%Z)) else ((intToBv) (1) (0%Z))) (((intToBv) (1) (0%Z)))))) then ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((intToBv) (64) (1%Z))) (tt)))) else if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (1) (if ((@SAWCoreVectorsAsCoqVectors.bvslt) (64) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (call_ret_val))) (((intToBv) (64) (0%Z)))) then ((intToBv) (1) ((-1)%Z)) else ((intToBv) (1) (0%Z))) (((intToBv) (1) (0%Z)))))) then ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((intToBv) (64) ((-1)%Z))) (tt)))) else ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((intToBv) (64) (0%Z))) (tt))))))))))) (tt))))).

Definition sign_of_sum : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@sign_of_sum__tuple_fun)))).

Definition compare_sum__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))))) (((@CompM.LRT_Nil))))) ((fun (compare_sum : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit))))))))))))))))) => ((pair) ((fun (p0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (p2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (tt) (if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvSBorrow) (63) (((intToBv) (64) (0%Z))) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (p0)))))) then ((((@bindM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@add_loop) (p1) (p2))) ((fun (call_ret_val : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((((@bindM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((@sign_of_sum) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@SAWCoreVectorsAsCoqVectors.bvSub) (64) (((intToBv) (64) (0%Z))) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (p0))))) (tt))) (call_ret_val))) ((fun (call_ret_val1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((((@returnM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (call_ret_val1)))))))) else ((((@errorM) (CompM) (_))) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (("Failed Assert at loops.c:28:22")%string)))))) (tt))))).

Definition compare_sum : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm0 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm1 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Fun) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) ((fun (perm2 : ((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) => ((@CompM.LRT_Ret) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@compare_sum__tuple_fun)))).

End loops.
