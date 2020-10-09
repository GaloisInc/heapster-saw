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

Definition bvMem_lo := intToBv 64 0xf000000000000000.
Definition bvMem_hi := intToBv 64 0x0fffffffffffffff.

Definition zero_array_precond x
  := isBvsle 64 (intToBv 64 0) x /\ isBvsle 64 x bvMem_hi.

Definition zero_array_invariant x x' (i : { _ & unit })
  := isBvsle 64 (intToBv 64 0) (projT1 i) /\ isBvsle 64 (projT1 i) x /\ x = x'.

Definition zero_array_noErrors_letRec : lrtToType zero_array_lrt := fun x _ =>
  assumingM (zero_array_precond x)
   (letRecM (lrts:=LRT_Cons zero_array_letRec_lrt LRT_Nil)
            (fun _ => (fun x' _ i => assumingM (zero_array_invariant x x' i)
                                     noErrorsSpec, tt))
            (fun _ => noErrorsSpec)).

Lemma no_errors_zero_array
  : refinesFun zero_array (fun x _ => assumingM (zero_array_precond x) noErrorsSpec).
Proof.
  transitivity zero_array_noErrors_letRec; try reflexivity.
  unfold zero_array, zero_array__tuple_fun, zero_array_noErrors_letRec, zero_array_letRec_lrt, zero_array_precond, zero_array_invariant, noErrorsSpec.
  unfold bvultWithProof.
  fold bvMem_lo; fold bvMem_hi.
  time "no_errors_zero_array" prove_refinement.
  (* A number of the remaining cases are covered exactly by hypotheses we already have in
     scope (e.g. proving the loop invariant holds initially). Note that `prove_refinement`
     doesn't do this automatically because it may matter which hypothesis is used, if
     there are multiple. For this poof though, it doesn't. *)
  all: try assumption.
  (* Proving that the loop invariant holds inductively: *)
  - transitivity a4.
    + assumption.
    + apply isBvsle_suc_r.
      rewrite e_assuming4, e_assuming1.
      reflexivity.
  - apply isBvslt_to_isBvsle_suc.
    rewrite <- e_assuming5 in e_if.
    apply isBvult_to_isBvslt_pos; assumption.
  (* Proving that these branches are impossible, by virtue of our loop invariant: *)
  - rewrite <- e_assuming2 in e_if0.
    discriminate e_if0.
  - rewrite e_assuming4, e_assuming1 in e_if0.
    apply isBvslt_antirefl in e_if0; contradiction e_if0.
  (* The remaining cases  are all
     taken care of by either prove_refinement or assmption! *)
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

Definition contains0_precond l
  := isBvsle 64 (intToBv 64 0) l /\ isBvsle 64 l bvMem_hi.

Definition contains0_invariant l l' (i : { _ & unit })
  := isBvsle 64 (intToBv 64 0) (projT1 i) /\ isBvsle 64 (projT1 i) l /\ l = l'.

Definition contains0_noErrors_letRec : lrtToType contains0_lrt := fun x _ =>
  assumingM (contains0_precond x)
   (letRecM (lrts:=LRT_Cons contains0_letRec_lrt LRT_Nil)
            (fun _ => (fun x' _ i => assumingM (contains0_invariant x x' i)
                                     noErrorsSpec, tt))
            (fun _ => noErrorsSpec)).

(* This proof is *identical* to no_errors_zero_array except for in the one noted spot *)
Lemma no_errors_contains0
  : refinesFun contains0 (fun x _ => assumingM (contains0_precond x) noErrorsSpec).
Proof.
  transitivity contains0_noErrors_letRec; try reflexivity.
  unfold contains0, contains0__tuple_fun, contains0_noErrors_letRec, contains0_letRec_lrt, contains0_precond, contains0_invariant, noErrorsSpec.
  unfold bvultWithProof.
  unfold true, false; fold bvMem_lo; fold bvMem_hi.
  time "no_errors_contains0" prove_refinement.
  all: try assumption.
  (* Different from no_errors_zero_array - this used to be taken care of by `prove_refinement`!
     (FIXME Figure out why this fails to be automated here but not above.) *)
  - rewrite e_if in e_maybe.
    discriminate e_maybe.
  - transitivity a4.
    + assumption.
    + apply isBvsle_suc_r.
      rewrite e_assuming4, e_assuming1.
      reflexivity.
  - apply isBvslt_to_isBvsle_suc.
    rewrite <- e_assuming5 in e_if.
    apply isBvult_to_isBvslt_pos; assumption.
  - rewrite <- e_assuming2 in e_if0.
    discriminate e_if0.
  - rewrite e_assuming4, e_assuming1 in e_if0.
    apply isBvslt_antirefl in e_if0; contradiction e_if0.
Qed.
