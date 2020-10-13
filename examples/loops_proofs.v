From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.loops.
Import loops.

Import SAWCorePrelude.


Lemma no_errors_add_loop : refinesFun add_loop (fun _ _ => noErrorsSpec).
Proof.
  unfold add_loop, add_loop__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ _ _ => noErrorsSpec).
  unfold noErrorsSpec.
  time "no_errors_add_loop" prove_refinement.
Qed.


Definition add_loop_spec (x y : {_ : bitvector 64 & unit}) : CompM {_ : bitvector 64 & unit}
  := returnM (existT _ (bvAdd 64 (projT1 x) (projT1 y)) tt).

Lemma add_loop_spec_ref : refinesFun add_loop add_loop_spec.
Proof.
  unfold add_loop, add_loop__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ ret i => add_loop_spec ret i).
  unfold add_loop_spec.
  time "add_loop_spec_ref" prove_refinement.
  - f_equal.
    rewrite bvAdd_assoc.
    rewrite (bvAdd_comm _ a5).
    rewrite <- (bvAdd_assoc _ _ _ a5).
    compute_bv_funs.
    rewrite bvAdd_id_l.
    reflexivity.
  - rewrite isBvule_n_zero in e_if.
    rewrite e_if, bvAdd_id_r.
    reflexivity.
Qed.
