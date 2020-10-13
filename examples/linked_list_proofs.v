From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.linked_list.
Import linked_list.

Import SAWCorePrelude.


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  time "no_errors_is_elem" prove_refinement.
Qed.

Lemma no_errors_is_elem_manual : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun.
  unfold noErrorsSpec.
  apply refinesFun_multiFixM_fst. intros x l. unfold refinesFun, Datatypes.fst.
  apply refinesM_letRecM_Nil_l.
  apply refinesM_either_l; intros.
  - eapply refinesM_existsM_r. reflexivity.
  - apply refinesM_if_l; intros.
    + eapply refinesM_existsM_r. reflexivity.
    + rewrite existsM_bindM.
      apply refinesM_existsM_l; intros. rewrite returnM_bindM.
      eapply refinesM_existsM_r. reflexivity.
Qed.

(*
Fixpoint is_elem_spec (x:bitvector 64) (l:W64List) : CompM {_:bitvector 64 & unit} :=
  match l with
  | W64Nil => returnM (existT _ (intToBv 64 0) tt)
  | W64Cons y l' =>
    if bvEq 64 y x then returnM (existT _ (intToBv 64 1) tt) else
      is_elem_spec x l'
  end.
*)

Definition is_elem_fun (x:bitvector 64) :
  list {_:bitvector 64 & unit} -> CompM {_:bitvector 64 & unit} :=
  list_rect (fun _ => CompM {_:bitvector 64 & unit})
            (returnM (existT _ (intToBv 64 0) tt))
            (fun y l' rec =>
               if bvEq 64 (projT1 y) x then returnM (existT _ (intToBv 64 1) tt) else rec).

Arguments is_elem_fun /.

Lemma is_elem_fun_ref : refinesFun is_elem is_elem_fun.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_fun, List_def.
  time "is_elem_fun_ref" prove_refinement.
Qed.

Lemma is_elem_fun_ref_manual : refinesFun is_elem is_elem_fun.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_fun.
  apply refinesFun_multiFixM_fst.
  apply refinesFunStep; intro x.
  apply refinesFunStep; intro l.
  destruct l; simpl; apply noDestructArg.
  - apply refinesM_letRecM_Nil_l.
    reflexivity.
  - apply refinesM_letRecM_Nil_l.
    apply refinesM_if_r; intro H; rewrite H; simpl.
    + reflexivity.
    + unshelve (rewrite_strat (bottomup (hints refinesM))).
      reflexivity.
Qed.

(* The pure version of is_elem *)
Definition is_elem_pure (x:bitvector 64) (l:list {_:bitvector 64 & unit})
  : {_:bitvector 64 & unit} :=
  (list_rect (fun _ => {_:bitvector 64 & unit})
             (existT _ (intToBv 64 0) tt)
             (fun y l' rec =>
                if bvEq 64 (projT1 y) x then existT _ (intToBv 64 1) tt else rec) l).

Arguments is_elem_pure /.

Definition is_elem_lrt : LetRecType :=
  LRT_Fun (bitvector 64) (fun _ =>
    LRT_Fun (list {_:bitvector 64 & unit}) (fun _ =>
      LRT_Ret {_:bitvector 64 & unit})).

Lemma is_elem_pure_fun_ref : @refinesFun is_elem_lrt is_elem_fun (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem_fun, is_elem_lrt, is_elem_pure.
  time "is_elem_pure_fun_ref" prove_refinement.
Qed.

Lemma is_elem_pure_fun_ref_manual : @refinesFun is_elem_lrt is_elem_fun (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem_fun, is_elem_pure.
  apply refinesFunStep; intro x.
  apply refinesFunStep; intro l.
  induction l; simpl; apply noDestructArg.
  - reflexivity.
  - apply refinesM_if_l; intro H; rewrite H.
    + reflexivity.
    + exact IHl.
Qed.

Lemma is_elem_pure_ref : refinesFun is_elem (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_pure, List_def.
  time "is_elem_pure_ref" prove_refinement.
Qed.


(* A high-level specification of is_elem *)
Definition is_elem_spec (x:bitvector 64) (l:list {_:bitvector 64 & unit})
  : CompM {_:bitvector 64 & unit} :=
  orM
    (assertM (List.In (existT _ x tt) l) >> returnM (existT _ (intToBv 64 1) tt))
    (assertM (~ List.In (existT _ x tt) l) >> returnM (existT _ (intToBv 64 0) tt)).

Arguments is_elem_spec /.

Lemma is_elem_spec_ref : refinesFun is_elem is_elem_spec.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_spec.
  time "is_elem_spec_ref" prove_refinement.
  (* First, some manipulation of e_either which knocks out a few cases: *)
  all: destruct a0; unfold unfoldList in e_either; simpl in e_either.
  all: try discriminate e_either.
  (* The a0 = [] case. *)
  - continue_prove_refinement_right.
    easy.
  (* Next, some destructing/simplification useful for the remaining cases: *)
  all: injection e_either as e_either_fst e_either_snd.
  all: rewrite e_either_fst, e_either_snd.
  all: simpl List.In.
  (* The a0 = (s1 :: a1) case where a = s1. *)
  - continue_prove_refinement_left.
    rewrite e_if.
    now left.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the left assertion of our specification *)
  - continue_prove_refinement_left.
    now right.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the right assertion of our specification *)
  - continue_prove_refinement_right.
    assert (deMorgan_inv : forall (P Q : Prop), ~ P /\ ~ Q -> ~ (P \/ Q)) by tauto.
    apply deMorgan_inv.
    split.
    + injection as not_e_if; contradiction.
    + assumption.
Qed.


Lemma refinesM_bind_lr A B (x y : CompM A) (f g : A -> CompM B) :
  refinesM x y -> @refinesFun (LRT_Fun A (fun _ => LRT_Ret B)) f g ->
  refinesM (x >>= f) (y >>= g).
Proof.
  unfold refinesM, bindM, MonadBindOp_OptionT, bindM, MonadBindOp_SetM.
  intros x_ref f_ref b H.
  destruct H as [ a xa H ].
  exists a.
  - apply x_ref.
    assumption.
  - destruct a.
    + apply f_ref.
      assumption.
    + assumption.
Qed.

Definition any_fun (f:{_:bitvector 64 & unit} -> CompM {_:bitvector 64 & unit}) :
  list {_:bitvector 64 & unit} -> CompM {_:bitvector 64 & unit} :=
  list_rect (fun _ => CompM {_:bitvector 64 & unit})
            (returnM (existT _ (intToBv 64 0) tt))
            (fun y l' rec =>
               f y >>= fun call_ret_val =>
                if not (bvEq 64 (projT1 call_ret_val) (intToBv 64 0))
                then returnM (existT _ (intToBv 64 1) tt) else rec).

Lemma any_fun_ref : refinesFun any any_fun.
Proof.
  unfold any, any__tuple_fun, any_fun.
  apply refinesFun_multiFixM_fst. intros f l.
  apply refinesM_letRecM_Nil_l.
  induction l.
  - reflexivity.
  - apply refinesM_bind_lr.
    + destruct a; destruct u; simpl.
      reflexivity.
    + time "any_fun_ref" prove_refinement.
Qed.


(*
Arguments sorted_insert__tuple_fun /.
Eval simpl in sorted_insert__tuple_fun.
Print sorted_insert__tuple_fun.
*)

Lemma no_errors_sorted_insert : refinesFun sorted_insert (fun _ _ => noErrorsSpec).
Proof.
  unfold sorted_insert, sorted_insert__tuple_fun, mallocSpec, noErrorsSpec.
  time "no_errors_sorted_insert" prove_refinement.
Qed.
