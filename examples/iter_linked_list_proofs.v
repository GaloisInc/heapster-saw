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

Ltac listF_destruct l l' := destruct l as [| ? l'].
Ltac listF_induction l l' := induction l as [| ? l'].
Ltac listF_simpl := simpl unfoldListF in *; simpl foldListF in *; simpl ListF__rec in *.

Hint Extern 2 (IntroArg ?n (eq (unfoldListF _ _ ?l)
                               (SAWCorePrelude.Left _ _ _)) _) =>
  doDestruction (listF_destruct) (listF_simpl) l : refinesFun.
Hint Extern 2 (IntroArg ?n (eq (unfoldListF _ _ ?l)
                               (SAWCorePrelude.Right _ _ _)) _) =>
  doDestruction (listF_destruct) (listF_simpl) l : refinesFun.

Hint Extern 9 (ListF__rec _ _ _ _ _ ?l |= _) =>
  doInduction (listF_induction) (listF_simpl) l : refinesFun.
Hint Extern 9 (_ |= ListF__rec _ _ _ _ _ ?l) =>
  doInduction (listF_induction) (listF_simpl) l : refinesFun.

Lemma transListF_NilF_r a b l x : transListF a b l (NilF a b x) = putListF a unit b l x.
Proof. induction l; eauto. Qed.

Lemma putListF_unit a l u : putListF a unit unit l u = l.
Proof. destruct u; induction l; [ destruct b | simpl; f_equal ]; eauto. Qed.

Hint Rewrite transListF_NilF_r putListF_unit : refinesM.


Definition incr_list_invar :=
  ListF__rec {_ : bitvector 64 & unit} unit (fun _ => Prop) (fun _ => True)
           (fun x _ rec => isBvult 64 (projT1 x) (intToBv 64 0x7fffffffffffffff) /\ rec).

Arguments incr_list_invar !l.

Lemma no_errors_incr_list :
  refinesFun incr_list (fun l => assumingM (incr_list_invar l) noErrorsSpec).
Proof.
  unfold incr_list, incr_list__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ l => assumingM (incr_list_invar l) noErrorsSpec).
  unfold noErrorsSpec.
  time "no_errors_incr_list" prove_refinement.
  (* All but one of the remaining goals are taken care of by assumptions we have in scope: *)
  all: try destruct e_assuming0 as [?e_assuming ?e_assuming]; try assumption.
  (* We just have to show this case is impossible by virtue of our loop invariant: *)
  apply isBvult_to_isBvule_suc in e_assuming0.
  apply bvule_msb_l in e_assuming0; try assumption.
  compute_bv_funs in e_assuming0; inversion e_assuming0.
Qed.
