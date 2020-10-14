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


(* Add `add_loop_spec_ref` to the hint database. Unfortunately, Coq will not unfold refinesFun
   and add_loop_spec when rewriting, and the only workaround I know right now is this :/ *)
Definition add_loop_spec_ref' : ltac:(let tp := type of add_loop_spec_ref in
                                      let tp' := eval unfold refinesFun, add_loop_spec in tp
                                       in exact tp') := add_loop_spec_ref.
Hint Rewrite add_loop_spec_ref' : refinesM.

Lemma no_errors_compare : refinesFun compare (fun _ _ => noErrorsSpec).
Proof.
  unfold compare, compare__tuple_fun, noErrorsSpec.
  time "no_errors_add_loop" prove_refinement.
Qed.

Definition compare_spec (x y : {_ : bitvector 64 & unit}) : CompM {_ : bitvector 64 & unit} :=
  orM (     assertM (isBvslt _ (intToBv _ 0) (bvAdd _ (projT1 x) (projT1 y)))
                    >> returnM (existT _ (intToBv _ 1) tt))
      (orM (assertM (isBvslt _ (bvAdd _ (projT1 x) (projT1 y)) (intToBv _ 0))
                    >> returnM (existT _ (intToBv _ (-1)) tt))
           (assertM (bvAdd _ (projT1 x) (projT1 y) = intToBv _ 0)
                    >> returnM (existT _ (intToBv _ 0) tt))).

Lemma compare_spec_ref : refinesFun compare compare_spec.
Proof.
  unfold compare, compare__tuple_fun, compare_spec.
  time "no_errors_add_loop" prove_refinement.
  - continue_prove_refinement_left.
    assumption.
  - continue_prove_refinement_right;
    continue_prove_refinement_left.
    assumption.
  - continue_prove_refinement_right;
    continue_prove_refinement_right.
    apply isBvsle_antisymm; assumption.
Qed.
