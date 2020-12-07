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


Lemma transListF_NilF_r a b l x : transListF a b l (NilF a b x) = putListF a unit b l x.
Proof. induction l; eauto. Qed.

Lemma putListF_unit a l u : putListF a unit unit l u = l.
Proof. destruct u; induction l; [ destruct b | simpl; f_equal ]; eauto. Qed.


Definition incr_list_invar :=
  ListF__rec {_ : bitvector 64 & unit} unit (fun _ => Prop) (fun _ => True)
           (fun x _ rec => isBvult 64 (projT1 x) (intToBv 64 0x7fffffffffffffff) /\ rec).

Lemma no_errors_incr_list :
  refinesFun incr_list (fun l => assumingM (incr_list_invar l) noErrorsSpec).
Proof.
  unfold incr_list, incr_list__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ l => assumingM (incr_list_invar l) noErrorsSpec).
  unfold noErrorsSpec.
  time "no_errors_incr_list" prove_refinement.
  (* Simplify the `incr_list_precond` cases and take care of some easy cases *)
  all: simpl; try rewrite transListF_NilF_r; repeat rewrite putListF_unit; try assumption.
  (* Destruct `a1` (relevant to all the remaining cases) *)
  all: destruct a1 as [[] | [? []] ?]; [ discriminate e_either | injection e_either as -> <- ].
  (* Destruct `e_assuming0` and take care of the remaining `incr_list_precond` cases *)
  all: destruct e_assuming0 as [e_assuming0 e_assuming1]; try assumption.
  (* Now all we need to show is that our invariant implies this case is impossible: *)
  unfold_projs in e_assuming0.
  apply isBvult_to_isBvule_suc in e_assuming0.
  apply bvule_msb_l in e_assuming0; try assumption.
  compute_bv_funs in e_assuming0; inversion e_assuming0.
Qed.
