From Coq          Require Import Program.Basics.
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Import SAWCorePrelude.

Require Import Examples.arrays.
Import arrays.

Import VectorNotations.

Lemma if_bv_lemma (b : bool) : not (bvEq 1 (if b then bvLit 1 1 else bvLit 1 0) (bvLit 1 0)) = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma and_bool_eq_true_lemma (b c : bool) : and b c = true <-> (b = true) /\ (c = true).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.

Lemma and_bool_eq_false_lemma (b c : bool) : and b c = false <-> (b = false) \/ (c = false).
Proof.
  split.
  - destruct b, c; auto.
  - intro; destruct H; destruct b, c; auto.
Qed.


(* Print zero_array__tuple_fun. *)

Definition zero_array_lrt
  := LRT_Fun (SAWCorePrelude.bitvector 64)
      (fun arg0 : SAWCorePrelude.bitvector 64 =>
       LRT_Fun (BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit})
         (fun _ : BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit} =>
          LRT_Ret (BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit}))).

Definition zero_array_letRec_lrt
  := LRT_Fun (SAWCorePrelude.bitvector 64)
      (fun arg0 : SAWCorePrelude.bitvector 64 =>
       LRT_Fun (BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit})
         (fun _ : BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit} =>
          LRT_Fun {_ : SAWCorePrelude.bitvector 64 & unit}
            (fun _ : {_ : SAWCorePrelude.bitvector 64 & unit} =>
             LRT_Ret (BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit})))).

Definition bvMem_lo :=
  Eval compute in bvLit_0b"1111000000000000000000000000000000000000000000000000000000000000".
Definition bvMem_hi :=
  Eval compute in bvLit_0b"0000111111111111111111111111111111111111111111111111111111111111".

Definition zero_array_noErrors : lrtToType zero_array_lrt := fun x _ =>
  assumingM (isBvsle 64 (bvLit 64 0) x /\ isBvsle 64 x bvMem_hi)
   (letRecM (lrts:=LRT_Cons zero_array_letRec_lrt LRT_Nil)
            (fun _ => (fun x' _ i => assumingM (   isBvsle 64 (bvLit 64 0) (projT1 i)
                                                /\ isBvsle 64 (projT1 i) x
                                                /\ x = x')
                                     noErrorsSpec, tt))
            (fun _ => noErrorsSpec)).

(* See no_errors_zero_array below, eventually we should get rid of this manual version *)
Lemma no_errors_zero_array_manual : refinesFun zero_array zero_array_noErrors.
Proof.
  unfold zero_array, zero_array__tuple_fun, zero_array_noErrors, noErrorsSpec.
  unfold zero_array_lrt, zero_array_letRec_lrt.
  unfold bvultWithProof.
  (* fold bvMem_lo and bvMem_hi for convenience (Why must I hold Coq's hand so much?? Aghhh!!) *)
  unfold true, false; fold bvMem_lo; fold bvMem_hi.
  (* unfold the top-level multiFixM on the left *)
  apply refinesFun_multiFixM_fst.
  unfold Datatypes.fst, refinesFun; intros.
  (* refinesM_assumingM_r, and manipulation of the resulting hyp. *)
  apply refinesM_assumingM_r; intro e_assuming1.
  destruct e_assuming1 as [ e_assuming1_H1 e_assuming1_H2 ].
  (* refinesM_letRecM1_fst *)
  apply refinesM_letRecM1_fst; try apply ProperFun_any.
  (* 1. proving refinement of the letRec'd functions *)
  - (* unfold the multiFixM on the left *)
    apply refinesFun_multiFixM_fst.
    unfold Datatypes.fst, refinesFun; intros.
    (* can we get Coq to do this auomatically too? *)
    rewrite if_bv_lemma.
    (* refinesM_assumingM_r, and manipulation of the resulting hyp. *)
    apply refinesM_assumingM_r; intro e_assuming2.
    destruct e_assuming2 as [ e_assuming2_H1 e_assuming2 ].
    destruct e_assuming2 as [ e_assuming2_H2 e_assuming2_H3 ].
    (* refinesM_if_l, and manipulation of the resulting hyp. *)
    apply refinesM_if_l; intro e_if1; try rewrite e_if1.
    + apply refinesM_if_l; intro e_if2.
      * apply refinesM_maybe_l; [ intro e_maybe | intros e_maybe_arg e_maybe ].
        -- discriminate e_maybe.
        -- apply refinesM_assumingM_l.
           (* I. proving the loop invariant *)
           ++ split; try split; cbn [ projT1 ].
              ** transitivity (projT1 a3).
                 --- assumption.
                 --- apply isBvsle_suc_r.
                     rewrite e_assuming2_H2, e_assuming1_H2.
                     reflexivity.
              ** apply isBvslt_to_isBvsle_suc.
                 rewrite isBvult_def in e_if1.
                 rewrite <- e_assuming2_H3 in e_if1.
                 apply isBvult_to_isBvslt_pos; assumption.
              ** assumption.
           (* II. proving refinement of the bodies *)
           ++ reflexivity.
      * (* this case is impossible *)
        rewrite and_bool_eq_false_lemma in e_if2.
        destruct e_if2 as [ e_if2 | e_if2 ]; rewrite isBvslt_def_opp in e_if2.
        -- rewrite <- e_assuming2_H1 in e_if2.
           vm_compute in e_if2; inversion e_if2.
        -- rewrite e_assuming2_H2, e_assuming1_H2 in e_if2.
           apply isBvslt_antirefl in e_if2; inversion e_if2.
    + prove_refinement.
  (* 2. proving refinement of the letRec bodies *)
  - apply refinesM_assumingM_l.
    (* I. proving the initial loop invariant *)
    + cbn [ projT1 ].
      split; split.
      * assumption.
      * reflexivity.
    (* II. proving refinement of the bodies *)
    + reflexivity.
Qed.

Lemma no_errors_zero_array : refinesFun zero_array zero_array_noErrors.
Proof.
  unfold zero_array, zero_array__tuple_fun, zero_array_noErrors, noErrorsSpec.
  unfold zero_array_lrt, zero_array_letRec_lrt.
  unfold bvultWithProof.
  unfold true, false; fold bvMem_lo; fold bvMem_hi.
  prove_refinement.
  (* Some cleanup which applies to multiple cases *)
  all: destruct e_assuming as [ e_assuming_H0 e_assuming_H1 ].
  all: try destruct e_assuming0 as [ e_assuming0_H0 e_assuming0 ].
  all: try destruct e_assuming0 as [ e_assuming0_H1 e_assuming0_H2 ].
  all: cbn [ projT1 ].
  - assumption. (* FIXME Could prove_refinement do this automatically? *)
  (* Maybe one day Heapster will be smart enough to know that this case is
     impossible, but for now it's easy enough prove: *)
  - rewrite if_bv_lemma in e_if.
    rewrite e_if in e_maybe.
    discriminate e_maybe.
  (* Proving the loop invariant holds inductively: *)
  - repeat split.
    + transitivity (projT1 a3).
      * assumption.
      * apply isBvsle_suc_r.
        rewrite e_assuming0_H1, e_assuming_H1.
        reflexivity.
    + apply isBvslt_to_isBvsle_suc.
      rewrite if_bv_lemma, isBvult_def in e_if.
      rewrite <- e_assuming0_H2 in e_if.
      apply isBvult_to_isBvslt_pos; assumption.
    + assumption.
  - assumption. (* FIXME Could prove_refinement do this automatically? *)
  (* Proving that this branch is impossible, by virtue of our loop invariant: *)
  - rewrite and_bool_eq_false_lemma in e_if0.
    destruct e_if0 as [ e_if0 | e_if0 ]; rewrite isBvslt_def_opp in e_if0.
    + rewrite <- e_assuming0_H0 in e_if0.
      vm_compute in e_if0.
      inversion e_if0.
    + rewrite e_assuming0_H1, e_assuming_H1 in e_if0.
      apply isBvslt_antirefl in e_if0; inversion e_if0.
  (* Proving the loop invariant holds initially (this is trivial) *)
  - repeat split; auto.
Qed.


Definition contains0_lrt
  := LRT_Fun (bitvector 64)
      (fun arg0 : bitvector 64 =>
       LRT_Fun (BVVec 64 arg0 {_ : bitvector 64 & unit})
         (fun _ : BVVec 64 arg0 {_ : bitvector 64 & unit} =>
          LRT_Ret
            (BVVec 64 arg0 {_ : bitvector 64 & unit} * ({_ : bitvector 64 & unit} * unit)))).

Definition contains0_letRec_lrt
  := LRT_Fun (bitvector 64)
      (fun arg0 : bitvector 64 =>
       LRT_Fun (BVVec 64 arg0 {_ : bitvector 64 & unit})
         (fun _ : BVVec 64 arg0 {_ : bitvector 64 & unit} =>
          LRT_Fun {_ : bitvector 64 & unit}
            (fun _ : {_ : bitvector 64 & unit} =>
             LRT_Ret
               (BVVec 64 arg0 {_ : bitvector 64 & unit} *
                ({_ : bitvector 64 & unit} * unit))))).

Definition contains0_noErrors : lrtToType contains0_lrt := fun l _ =>
  assumingM (isBvsle 64 (bvLit 64 0) l /\ isBvsle 64 l bvMem_hi)
   (letRecM (lrts:=LRT_Cons contains0_letRec_lrt LRT_Nil)
            (fun _ => (fun l' _ i => assumingM (   isBvsle 64 (bvLit 64 0) (projT1 i)
                                                /\ isBvsle 64 (projT1 i) l
                                                /\ l = l')
                                     noErrorsSpec, tt))
            (fun _ => noErrorsSpec)).

(* This proof is *identical* to no_errors_zero_array except for in the two noted spots *)
Lemma no_errors_contains0 : refinesFun contains0 contains0_noErrors.
Proof.
  unfold contains0, contains0__tuple_fun, contains0_noErrors, noErrorsSpec.
  unfold contains0_lrt, contains0_letRec_lrt.
  unfold bvultWithProof.
  unfold true, false; fold bvMem_lo; fold bvMem_hi.
  prove_refinement.
  all: destruct e_assuming as [ e_assuming_H0 e_assuming_H1 ].
  all: try destruct e_assuming0 as [ e_assuming0_H0 e_assuming0 ].
  all: try destruct e_assuming0 as [ e_assuming0_H1 e_assuming0_H2 ].
  all: cbn [ projT1 ].
  - repeat (split; try assumption). (* <- different from no_errors_zero_array *)
  - rewrite if_bv_lemma in e_if.
    rewrite e_if in e_maybe.
    discriminate e_maybe.
  - repeat split.
    + transitivity (projT1 a3).
      * assumption.
      * apply isBvsle_suc_r.
        rewrite e_assuming0_H1, e_assuming_H1.
        reflexivity.
    + apply isBvslt_to_isBvsle_suc.
      rewrite if_bv_lemma, isBvult_def in e_if.
      rewrite <- e_assuming0_H2 in e_if.
      apply isBvult_to_isBvslt_pos; assumption.
    + assumption.
  - repeat (split; try assumption). (* <- different from no_errors_zero_array *)
  - rewrite and_bool_eq_false_lemma in e_if0.
    destruct e_if0 as [ e_if0 | e_if0 ]; rewrite isBvslt_def_opp in e_if0.
    + rewrite <- e_assuming0_H0 in e_if0.
      vm_compute in e_if0.
      inversion e_if0.
    + rewrite e_assuming0_H1, e_assuming_H1 in e_if0.
      apply isBvslt_antirefl in e_if0; inversion e_if0.
  - repeat split; auto.
Qed.
