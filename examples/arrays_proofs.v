From Coq          Require Import Program.Basics.
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

Import VectorNotations.

Lemma if_bv_lemma (b : bool) : not (bvEq 1 (if b then bvLit 1 1 else bvLit 1 0) (bvLit 1 0)) = b.
Proof.
  destruct b; reflexivity.
Qed.

Definition bvInRange w (x lo hi : SAWCorePrelude.bitvector w) :=
  and (bvsle w lo x) (bvsle w x hi).

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

Definition isBvsle w a b : Prop := bvsle w a b = true.
Definition isBvsle_def w a b : bvsle w a b = true <-> isBvsle w a b := reflexivity _.
Definition isBvsle_def_opp w a b : bvslt w a b = false <-> isBvsle w b a. Admitted.
Instance PreOrder_isBvsle w : PreOrder (isBvsle w). Admitted.

Definition isBvsle_suc_r w (a : bitvector w) : isBvsle w a (bvAdd w a (bvLit w 1)).
Admitted.

Definition isBvslt w a b : Prop := bvslt w a b = true.
Definition isBvslt_def w a b : bvslt w a b = true <-> isBvslt w a b := reflexivity _.
Definition isBvslt_def_opp w a b : bvsle w a b = false <-> isBvslt w b a. Admitted.
Instance PreOrder_isBvslt w : PreOrder (isBvslt w). Admitted.

Instance Proper_isBvslt_isBvsle w : Proper (isBvsle w --> isBvsle w ==> impl) (isBvslt w).
Admitted.

Definition isBvslt_to_isBvsle_suc w a b : isBvslt w a b -> isBvsle w (bvAdd w a (bvLit w 1)) b.
Admitted.

Definition isBvslt_antirefl w a : ~ isBvslt w a a.
Admitted.

Definition isBvule w a b : Prop := bvule w a b = true.
Definition isBvule_def w a b : bvule w a b = true <-> isBvule w a b := reflexivity _.
Definition isBvule_def_opp w a b : bvult w a b = false <-> isBvule w b a. Admitted.
Instance PreOrder_isBvule w : PreOrder (isBvule w). Admitted.

Definition isBvult w a b : Prop := bvult w a b = true.
Definition isBvult_def w a b : bvult w a b = true <-> isBvult w a b := reflexivity _.
Definition isBvult_def_opp w a b : bvule w a b = false <-> isBvult w b a. Admitted.
Instance PreOrder_isBvult w : PreOrder (isBvult w). Admitted.

Definition isBvult_to_isBvslt_pos w a b : isBvsle w (bvLit w 0) a ->
                                          isBvsle w (bvLit w 0) b ->
                                          isBvult w a b -> isBvslt w a b.
Admitted.


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
  assumingM (bvInRange 64 x (bvLit 64 0) bvMem_hi = true)
   (letRecM (lrts:=LRT_Cons zero_array_letRec_lrt LRT_Nil)
            (fun _ => (fun x' _ i => assumingM (bvInRange 64 (projT1 i) (bvLit 64 0) x = true
                                                /\ x = x')
                                     noErrorsSpec, tt))
            (fun _ => noErrorsSpec)).

(* Set Typeclasses Debug. *)

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
  unfold bvInRange in e_assuming1.
  rewrite and_bool_eq_true_lemma in e_assuming1.
  repeat rewrite isBvsle_def in e_assuming1.
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
    apply refinesM_assumingM_r; intro e_assuming2; unfold bvInRange in e_assuming2.
    rewrite and_bool_eq_true_lemma in e_assuming2.
    destruct e_assuming2 as [ e_assuming2 e_assuming2_H3 ].
    repeat rewrite isBvsle_def in e_assuming2.
    destruct e_assuming2 as [ e_assuming2_H1 e_assuming2_H2 ].
    (* refinesM_if_l, and manipulation of the resulting hyp. *)
    apply refinesM_if_l; intro e_if1; try rewrite e_if1.
    + apply refinesM_if_l; intro e_if2.
      * apply refinesM_maybe_l; [ intro e_maybe | intros e_maybe_arg e_maybe ].
        -- discriminate e_maybe.
        -- apply refinesM_assumingM_l.
           (* I. proving the loop invariant *)
           ++ unfold bvInRange.
              rewrite and_bool_eq_true_lemma.
              split; try split; try rewrite isBvsle_def.
              ** transitivity (projT1 a3).
                 --- assumption.
                 --- apply isBvsle_suc_r.
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
    + unfold projT1, bvInRange.
      rewrite and_bool_eq_true_lemma; split; split.
      * reflexivity.
      * assumption.
    (* II. proving refinement of the bodies *)
    + reflexivity.
Qed.

Lemma no_errors_zero_array_auto : refinesFun zero_array zero_array_noErrors.
Proof.
  unfold zero_array, zero_array__tuple_fun, zero_array_noErrors, noErrorsSpec.
  unfold zero_array_lrt, zero_array_letRec_lrt.
  unfold bvultWithProof.
  unfold true, false; fold bvMem_lo; fold bvMem_hi.
  (* apply refinesFun_multiFixM_fst. *)
  (* unfold Datatypes.fst, refinesFun; intros. *)
  (* apply refinesM_assumingM_r; intro e_assuming. *)
  prove_refinement.
  (* Some hypothesis cleanup used in most of the below cases *)
  all: try unfold bvInRange in e_assuming, e_assuming0.
  all: try rewrite and_bool_eq_true_lemma in e_assuming, e_assuming0.
  all: try repeat rewrite isBvsle_def in e_assuming, e_assuming0.
  all: try destruct e_assuming  as [ e_assuming_H0 e_assuming_H1 ].
  all: try destruct e_assuming0 as [ e_assuming0 e_assuming0_H2 ].
  all: try destruct e_assuming0 as [ e_assuming0_H0 e_assuming0_H1 ].
  - assumption. (* FIXME Could prove_refinement do this automatically? *)
  - rewrite if_bv_lemma in e_if.
    rewrite e_if in e_maybe.
    discriminate e_maybe.
  - (* Proving the loop invariant holds inductively: *)
    simpl; unfold bvInRange.
    rewrite and_bool_eq_true_lemma.
    split; try split; try rewrite isBvsle_def.
    + transitivity (projT1 a3).
      * assumption.
      * apply isBvsle_suc_r.
    + apply isBvslt_to_isBvsle_suc.
      rewrite if_bv_lemma, isBvult_def in e_if.
      rewrite <- e_assuming0_H2 in e_if.
      apply isBvult_to_isBvslt_pos; assumption.
    + assumption.
  - assumption. (* FIXME Could prove_refinement do this automatically? *)
  - (* Proving that this case is absurd, by virtue of out loop invariant: *)
    rewrite and_bool_eq_false_lemma in e_if0.
    destruct e_if0 as [ e_if0 | e_if0 ]; rewrite isBvslt_def_opp in e_if0.
    + rewrite <- e_assuming0_H0 in e_if0.
      vm_compute in e_if0.
      inversion e_if0.
    + rewrite e_assuming0_H1, e_assuming_H1 in e_if0.
      apply isBvslt_antirefl in e_if0; inversion e_if0.
  - (* Proving the loop invariant holds initially: *)
    split.
    + admit. (* FIXME Hunh?? Is Coq deleting the e_assuming hypothesis...? *)
    + reflexivity.
Admitted.


Definition contains0_lrt := (LRT_Fun (SAWCorePrelude.bitvector 64)
                   (fun arg0 : SAWCorePrelude.bitvector 64 =>
                    LRT_Fun (BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit})
                      (fun _ : BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit} =>
                       LRT_Fun {_ : SAWCorePrelude.bitvector 64 & unit}
                         (fun _ : {_ : SAWCorePrelude.bitvector 64 & unit} =>
                          LRT_Ret
                            (BVVec 64 arg0 {_ : SAWCorePrelude.bitvector 64 & unit} *
                             ({_ : SAWCorePrelude.bitvector 64 & unit} * unit)))))).

Lemma no_errors_contains0 : refinesFun contains0 (fun _ _ => letRecM (lrts:=LRT_Cons contains0_lrt LRT_Nil) (fun _ => (fun _ _ _ => noErrorsSpec, tt)) (fun _ => noErrorsSpec)).
Proof.
  unfold contains0, contains0__tuple_fun, noErrorsSpec.
Admitted.
