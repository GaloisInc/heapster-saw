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

(* Print add_loop__tuple_fun. *)

Definition add_loop_lrt
  := LRT_Fun {_ : bitvector 64 & unit}
      (fun _ : {_ : bitvector 64 & unit} =>
       LRT_Fun {_ : bitvector 64 & unit}
         (fun _ : {_ : bitvector 64 & unit} =>
            LRT_Ret {_ : bitvector 64 & unit})).

Definition add_loop_letRec_lrt
  := LRT_Fun {_ : bitvector 64 & unit}
      (fun _ : {_ : bitvector 64 & unit} =>
       LRT_Fun {_ : bitvector 64 & unit}
         (fun _ : {_ : bitvector 64 & unit} =>
          LRT_Fun {_ : bitvector 64 & unit}
            (fun _ : {_ : bitvector 64 & unit} =>
             LRT_Fun {_ : bitvector 64 & unit}
               (fun _ : {_ : bitvector 64 & unit} =>
                LRT_Ret {_ : bitvector 64 & unit})))).

Definition add_loop_noErrors_letRec : lrtToType add_loop_lrt := fun _ _ =>
   letRecM (lrts:=LRT_Cons add_loop_letRec_lrt LRT_Nil)
           (fun _ => (fun _ _ _ _ => noErrorsSpec, tt))
           (fun _ => noErrorsSpec).

Lemma no_errors_add_loop : refinesFun add_loop (fun _ _ => noErrorsSpec).
Proof.
  transitivity add_loop_noErrors_letRec; try reflexivity.
  unfold add_loop, add_loop__tuple_fun, add_loop_noErrors_letRec, noErrorsSpec.
  prove_refinement.
Qed.
