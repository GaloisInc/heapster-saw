From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.linked_list.
Import linked_list.

Import SAWCorePrelude.


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  prove_refinement.
Qed.

Lemma no_errors_is_elem_manual : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun.
  unfold noErrorsSpec.
  apply refinesFun_multiFixM_fst. intros x l. unfold refinesFun, Datatypes.fst.
  apply refinesM_letRecM0.
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
  | W64Nil => returnM (existT _ (bvNat 64 0) tt)
  | W64Cons y l' =>
    if bvEq 64 y x then returnM (existT _ (bvNat 64 1) tt) else
      is_elem_spec x l'
  end.
*)

Definition is_elem_fun (x:bitvector 64) :
  list {_:bitvector 64 & unit} -> CompM {_:bitvector 64 & unit} :=
  list_rect (fun _ => CompM {_:bitvector 64 & unit})
            (returnM (existT _ (bvNat 64 0) tt))
            (fun y l' rec =>
               if bvEq 64 (projT1 y) x then returnM (existT _ (bvNat 64 1) tt) else rec).

Arguments is_elem_fun /.

Lemma is_elem_fun_ref : refinesFun is_elem is_elem_fun.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_fun.
  prove_refinement.
Qed.

Lemma is_elem_fun_ref_manual : refinesFun is_elem is_elem_fun.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_fun.
  apply refinesFun_multiFixM_fst.
  apply refinesFunStep; intro x.
  apply refinesFunStep; intro l.
  destruct l; simpl; apply noDestructArg.
  - apply refinesM_letRecM0.
    reflexivity.
  - apply refinesM_letRecM0.
    apply refinesM_if_r; intro H; rewrite H; simpl.
    + reflexivity.
    + setoid_rewrite existT_eta_unit.
      setoid_rewrite bindM_returnM_CompM.
      reflexivity.
Qed.

(* The pure version of is_elem *)
Definition is_elem_pure (x:bitvector 64) (l:list {_:bitvector 64 & unit})
  : {_:bitvector 64 & unit} :=
  (list_rect (fun _ => {_:bitvector 64 & unit})
             (existT _ (bvNat 64 0) tt)
             (fun y l' rec =>
                if bvEq 64 (projT1 y) x then existT _ (bvNat 64 1) tt else rec) l).

Arguments is_elem_pure /.

Definition is_elem_lrt : LetRecType :=
  LRT_Fun (bitvector 64) (fun _ =>
    LRT_Fun (list {_:bitvector 64 & unit}) (fun _ =>
      LRT_Ret {_:bitvector 64 & unit})).

Lemma is_elem_pure_fun_ref : @refinesFun is_elem_lrt is_elem_fun (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem_fun, is_elem_pure.
  prove_refinement.
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
  unfold is_elem, is_elem__tuple_fun, is_elem_pure.
  prove_refinement.
Qed.


(* Lemmas needed for is_elem_spec_ref *)
Section Lemmas_is_elem_spec_ref.

  Lemma if_bvEq_lemma s1 a b :
    not (bvEq 1 (if bvEq 64 s1 a then bvNat 1 1 else bvNat 1 0) (bvNat 1 0)) = b ->
    bvEq 64 s1 a = b.
  Proof. destruct (bvEq 64 s1 a). auto. auto. Qed.

  (* Require Import Coq.Program.Equality. *)

  Lemma bv_eq_impl_eq k : forall x y, bvEq k x y = true -> x = y.
  Proof.
    unfold bitvector, bvEq, boolEq.
    (* dependent induction x; dependent induction y.
    - reflexivity.
    - admit. *)
  Admitted.

  Lemma bv_neq_impl_neq k : forall x y, bvEq k x y = false -> x <> y.
  Proof.
    unfold bitvector, bvEq, boolEq.
    (*
    dependent induction x; dependent induction y.
    - discriminate.
    - admit. *)
  Admitted.

  Lemma deMorgan_inv (P Q : Prop) : ~ P /\ ~ Q -> ~ (P \/ Q).
  Proof.
    intros nPnQ PQ.
    destruct nPnQ as [nP nQ]; destruct PQ.
    - apply nP. assumption.
    - apply nQ. assumption.
  Qed.

End Lemmas_is_elem_spec_ref.


Definition orM {A} (m1 m2:CompM A) : CompM A :=
  existsM (fun (b:bool) => if b then m1 else m2).

Definition assertM (P:Prop) : CompM unit :=
  existsM (fun (_:P) => returnM tt).

(* The specification of is_elem: returns 1 if  *)
Definition is_elem_spec (x:bitvector 64) (l:list {_:bitvector 64 & unit})
  : CompM {_:bitvector 64 & unit} :=
  orM
    (assertM (List.In (existT _ x tt) l) >> returnM (existT _ (bvNat 64 1) tt))
    (assertM (~ List.In (existT _ x tt) l) >> returnM (existT _ (bvNat 64 0) tt)).

Arguments is_elem_spec /.

Lemma is_elem_spec_ref : refinesFun is_elem is_elem_spec.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_spec.
  prove_refinement.
  (* do some simplification of e_either relevant to every case *)
  all: destruct a0; unfold unfoldList in e_either; simpl in e_either.
  all: try discriminate e_either.
  all: try injection e_either; clear e_either; intro e_either.

  (* The a0 = [] case *)
  - unfold orM, assertM; prove_refinement.
    + exact Datatypes.false.
    + unfold List.In.
      prove_refinement.
      auto.

  (* do some destructing useful for the remaining cases *)
  all: destruct b as [s1 b]; destruct b as [a1 t]; destruct t.
  all: destruct s1 as [s1 t]; destruct t; simpl in e_if.
  all: apply if_bvEq_lemma in e_if.

  (* The a0 = (s1 :: a1) case where a = s1 *)
  - unfold orM, assertM; prove_refinement.
    + exact Datatypes.true.
    + prove_refinement.
      left.
      apply (f_equal fst) in e_either; simpl in e_either.
      rewrite e_either.
      apply bv_eq_impl_eq in e_if.
      rewrite e_if.
      reflexivity.

  (* The a0 = (s1 :: a1) case where a <> s1 *)
  - pose (e_either0 := f_equal fst e_either); simpl in e_either0.
    pose (e_either1 := f_equal (fun x => fst (snd x)) e_either); simpl in e_either1.
    rewrite e_either0, e_either1.
    apply bv_neq_impl_neq in e_if.
    unfold orM, assertM.
    apply refinesM_existsM_lr; intro b.
    prove_refinement.
    + right. assumption.
    + simpl. apply deMorgan_inv.
      split; auto.
      intro p.
      injection p.
      assumption.
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
            (returnM (existT _ (bvNat 64 0) tt))
            (fun y l' rec =>
               f y >>= fun call_ret_val =>
                if not (bvEq 64 (projT1 call_ret_val) (bvNat 64 0))
                then returnM (existT _ (bvNat 64 1) tt) else rec).

Lemma any_fun_ref : refinesFun any any_fun.
Proof.
  unfold any, any__tuple_fun, any_fun.
  apply refinesFun_multiFixM_fst. intros f l.
  apply refinesM_letRecM0.
  induction l.
  - reflexivity.
  - apply refinesM_bind_lr.
    + destruct a; destruct u; simpl.
      reflexivity.
    + prove_refinement.
Qed.


Arguments sorted_insert__tuple_fun /.
Eval simpl in sorted_insert__tuple_fun.
Print sorted_insert__tuple_fun.

Lemma no_errors_sorted_insert : refinesFun sorted_insert (fun _ _ => noErrorsSpec).
Proof.
  unfold sorted_insert, sorted_insert__tuple_fun, malloc, mallocSpec, noErrorsSpec.
  prove_refinement.
Qed.
