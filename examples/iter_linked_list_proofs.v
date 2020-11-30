From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.iter_linked_list.
Import iter_linked_list.

Import SAWCorePrelude.

Lemma no_errors_incr_list : refinesFun incr_list (fun _ => noErrorsSpec).
Proof.
  unfold incr_list, incr_list__tuple_fun.
  (* prove_refinement_match_letRecM_l. *)
Admitted.
