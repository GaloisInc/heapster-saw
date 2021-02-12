
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module rust_lifetimes.

Definition int8Trans : Type :=
  @sigT (@SAWCorePrelude.bitvector 8) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool)) => unit).

Definition int64Trans : Type :=
  @sigT (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit).

Definition mkInt64Trans : @SAWCorePrelude.bitvector 64 -> @int64Trans :=
  fun (bv : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @existT (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) bv tt.

Definition unfoldListPermH : forall (a : Type), @Datatypes.list a -> @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) :=
  fun (a : Type) (l : @Datatypes.list a) => @Datatypes.list_rect a (fun (_1 : @Datatypes.list a) => @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) (@SAWCorePrelude.Left unit (prod unit (prod a (@Datatypes.list a))) tt) (fun (x : a) (l1 : @Datatypes.list a) (_1 : @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) => @SAWCorePrelude.Right unit (prod unit (prod a (@Datatypes.list a))) (pair tt (pair x l1))) l.

Definition foldListPermH : forall (a : Type), @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) -> @Datatypes.list a :=
  fun (a : Type) => @SAWCorePrelude.either unit (prod unit (prod a (@Datatypes.list a))) (@Datatypes.list a) (fun (_1 : unit) => @Datatypes.nil a) (fun (tup : prod unit (prod a (@Datatypes.list a))) => @Datatypes.cons a (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd tup)) (SAWCoreScaffolding.snd (SAWCoreScaffolding.snd tup))).

Definition mux_mut_refs_u64__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))))) (@CompM.LRT_Nil)) (fun (mux_mut_refs_u64 : @CompM.lrtToType (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))))))) => pair (fun (p0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (p1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (p2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) tt (if @SAWCoreScaffolding.not (@SAWCorePrelude.bvEq 1 (@projT1 (@SAWCorePrelude.bitvector 1) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 1) => unit) p2) (intToBv 1 0%Z)) then @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) p0 else @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) p1)) tt).

Definition mux_mut_refs_u64 : @CompM.lrtToType (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))))) :=
  SAWCoreScaffolding.fst (@mux_mut_refs_u64__tuple_fun).

End rust_lifetimes.
