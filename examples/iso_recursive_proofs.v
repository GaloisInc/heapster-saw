From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.iso_recursive.
Import iso_recursive.

Import SAWCorePrelude.

Ltac listIRT_destruct l l' := destruct l as [| ? l'].
Ltac listIRT_induction l l' := induction l as [| ? l'].
Ltac listIRT_simpl := simpl unfoldListIRT in *; simpl foldListIRT in *.

Hint Extern 2 (IntroArg ?n (eq (unfoldListIRT _ _ ?l)
                               (SAWCorePrelude.Left _ _ _)) _) =>
  doDestruction (listIRT_destruct) (listIRT_simpl) l : refinesFun.
Hint Extern 2 (IntroArg ?n (eq (unfoldListIRT _ _ ?l)
                               (SAWCorePrelude.Right _ _ _)) _) =>
  doDestruction (listIRT_destruct) (listIRT_simpl) l : refinesFun.


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  time "no_errors_is_elem (IRT)" prove_refinement.
Qed.
