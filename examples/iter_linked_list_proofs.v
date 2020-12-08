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

Definition Bit__rec : forall (p : @Bit -> Type), p (@Bit1) -> p (@Bit0) -> forall (b : @Bit), p b :=
  fun (p : @Bit -> Type) (f1 : p (@Bit1)) (f2 : p (@Bit0)) (b : @Bit) => SAWCorePrelude.Bit_rect p f1 f2 b.


Lemma no_errors_incr_list : refinesFun incr_list (fun _ => noErrorsSpec).
Proof.
  unfold incr_list, incr_list__tuple_fun.
  (* prove_refinement_match_letRecM_l. *)
Admitted.
