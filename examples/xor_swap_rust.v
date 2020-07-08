
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module xor_swap_rust.

Definition xor_swap_rust__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg1 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Ret) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))))))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg1 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Ret) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))))))))))) (((@CompM.LRT_Nil))))) ((fun (xor_swap_rust : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg1 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Ret) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))))))))))))) => ((pair) ((fun (e0 : ((@SAWCorePrelude.bitvector) (64))) (e1 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.letRecM) (((@CompM.LRT_Nil))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))) (tt) (((((@returnM) (CompM) (_))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))) (((pair) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@SAWCorePrelude.bvXor) (64) (((@SAWCorePrelude.bvXor) (64) (e0) (e1))) (((@SAWCorePrelude.bvXor) (64) (((@SAWCorePrelude.bvXor) (64) (e0) (e1))) (e1))))) (tt))) (((pair) (((@existT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((@SAWCorePrelude.bvXor) (64) (((@SAWCorePrelude.bvXor) (64) (e0) (e1))) (e1))) (tt))) (tt)))))))))) (tt))))).

Definition xor_swap_rust : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg0 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Fun) (((@SAWCorePrelude.bitvector) (64))) ((fun (arg1 : ((@SAWCorePrelude.bitvector) (64))) => ((@CompM.LRT_Ret) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit)))))))))))))) :=
  ((SAWCoreScaffolding.fst) (((@xor_swap_rust__tuple_fun)))).

End xor_swap_rust.
