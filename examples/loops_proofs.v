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


Lemma no_errors_add_loop : refinesFun add_loop (fun _ _ => noErrorsSpec).
Proof.
  transitivity ((fun _ _ => letRecM (lrts:=LRT_Cons add_loop_letRec_lrt LRT_Nil)
                                    (fun _ => (fun _ _ _ _ => noErrorsSpec, tt))
                                    (fun _ => noErrorsSpec)) : lrtToType add_loop_lrt);
               try reflexivity.
  unfold add_loop, add_loop__tuple_fun, noErrorsSpec.
  prove_refinement.
Qed.


Definition add_loop_spec : lrtToType add_loop_lrt
  := fun x y => returnM (existT _ (bvAdd 64 (projT1 x) (projT1 y)) tt).

Lemma add_loop_spec_ref : refinesFun add_loop add_loop_spec.
Proof.
  transitivity (fun x y => letRecM (lrts:=LRT_Cons add_loop_letRec_lrt LRT_Nil)
                                   (fun _ => (fun _ _ ret i => add_loop_spec ret i, tt))
                                   (fun _ => add_loop_spec x y));
               try reflexivity.
  unfold add_loop, add_loop__tuple_fun, add_loop_spec, noErrorsSpec.
  prove_refinement; cbn [ projT1 ].
  - f_equal.
    rewrite bvAdd_assoc.
    rewrite (bvAdd_comm _ (projT1 a4)).
    rewrite <- (bvAdd_assoc _ _ _ (projT1 a4)).
    unfold true, false.
    (* The next three lines could just be replaced by `vm_compute bvAdd at 3`,
       but then `Qed` hangs... *)
    assert (bvAdd 64 (bvLit 64 1) (bvLit 64 (-1)) = bvLit 64 0) as H by reflexivity.
    vm_compute bvLit in H.
    rewrite H.
    rewrite bvAdd_id_l.
    reflexivity.
  - rewrite isBvule_n_zero in e_if.
    rewrite e_if, bvAdd_id_r.
    destruct a3 as [ projT1_a3 u ]; destruct u; simpl.
    reflexivity.
Qed.
