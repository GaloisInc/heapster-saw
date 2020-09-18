From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Import SAWCorePrelude.

Require Import Examples.arrays.
Import arrays.

Lemma no_errors_contains0 : refinesFun contains0 (fun _ _ => noErrorsSpec).
Proof.
  unfold contains0, contains0__tuple_fun, noErrorsSpec.
Admitted.

Lemma no_errors_zero_array : refinesFun zero_array (fun _ _ => noErrorsSpec).
Proof.
  unfold zero_array, zero_array__tuple_fun, noErrorsSpec.
Admitted.
