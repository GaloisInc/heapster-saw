
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module rust_lifetimes.

Definition int1Trans : Type :=
  @sigT (@SAWCorePrelude.bitvector 1) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit).

Definition mkInt1Trans : @SAWCorePrelude.bitvector 1 -> @int1Trans :=
  fun (bv : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => @existT (@SAWCorePrelude.bitvector 1) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit) bv tt.

Definition unInt1Trans : @int1Trans -> @SAWCorePrelude.bitvector 1 :=
  fun (bv : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit)) => @projT1 (@SAWCorePrelude.bitvector 1) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit) bv.

Definition int8Trans : Type :=
  @sigT (@SAWCorePrelude.bitvector 8) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool)) => unit).

Definition int64Trans : Type :=
  @sigT (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit).

Definition mkInt64Trans : @SAWCorePrelude.bitvector 64 -> @int64Trans :=
  fun (bv : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @existT (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) bv tt.

Definition unInt64Trans : @int64Trans -> @SAWCorePrelude.bitvector 64 :=
  fun (bv : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) => @projT1 (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) bv.

Definition unfoldListPermH : forall (a : Type), @Datatypes.list a -> @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) :=
  fun (a : Type) (l : @Datatypes.list a) => @Datatypes.list_rect a (fun (_1 : @Datatypes.list a) => @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) (@SAWCorePrelude.Left unit (prod unit (prod a (@Datatypes.list a))) tt) (fun (x : a) (l1 : @Datatypes.list a) (_1 : @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) => @SAWCorePrelude.Right unit (prod unit (prod a (@Datatypes.list a))) (pair tt (pair x l1))) l.

Definition foldListPermH : forall (a : Type), @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) -> @Datatypes.list a :=
  fun (a : Type) => @SAWCorePrelude.either unit (prod unit (prod a (@Datatypes.list a))) (@Datatypes.list a) (fun (_1 : unit) => @Datatypes.nil a) (fun (tup : prod unit (prod a (@Datatypes.list a))) => @Datatypes.cons a (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd tup)) (SAWCoreScaffolding.snd (SAWCoreScaffolding.snd tup))).

Definition llvm__x2euadd__x2ewith__x2eoverflow__x2ei64 : forall (p0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)), forall (p1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @SAWCorePrelude.bitvector 1 in
  CompM (prod (@sigT var__0 (fun (x_ex0 : var__0) => unit)) (prod (@sigT var__1 (fun (x_ex0 : var__1) => unit)) unit)) :=
  fun (x : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) (y : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) => @returnM CompM _ (prod (@int64Trans) (prod (@int1Trans) unit)) (pair (@mkInt64Trans (@SAWCoreVectorsAsCoqVectors.bvAdd 64 (@unInt64Trans x) (@unInt64Trans y))) (pair (@mkInt1Trans (@SAWCoreVectorsAsCoqVectors.gen 1 (@SAWCoreScaffolding.Bool) (fun (_1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.bvCarry 64 (@unInt64Trans x) (@unInt64Trans y)))) tt)).

Definition llvm__x2eexpect__x2ei1 : forall (p0 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)), forall (p1 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)), let var__0   := @SAWCorePrelude.bitvector 1 in
  CompM (@sigT var__0 (fun (x_ex0 : var__0) => unit)) :=
  fun (x : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit)) (y : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit)) => @returnM CompM _ (@int1Trans) x.

Definition mux_mut_refs_u64__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))))) (@CompM.LRT_Nil)) (fun (mux_mut_refs_u64 : @CompM.lrtToType (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))))))) => pair (fun (p0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (p1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (p2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) tt (if @SAWCoreScaffolding.not (@SAWCorePrelude.bvEq 1 (@projT1 (@SAWCorePrelude.bitvector 1) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 1) => unit) p2) (intToBv 1 0%Z)) then @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) p0 else @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) p1)) tt).

Definition mux_mut_refs_u64 : @CompM.lrtToType (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))))) :=
  SAWCoreScaffolding.fst (@mux_mut_refs_u64__tuple_fun).

Definition use_mux_mut_refs__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (@CompM.LRT_Nil)) (fun (use_mux_mut_refs : @CompM.lrtToType (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => pair (@CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) tt (@bindM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@mux_mut_refs_u64 (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 5%Z) tt) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 0x2a%Z) tt) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (intToBv 1 (-1)%Z) tt)) (fun (call_ret_val : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @errorM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) "At internal ($2 = load llvm_memory $1 bitvectorType 8 Alignment 3)
  Regs: $1 = local2
  Input perms: ghost3:llvmframe [local1:8, ghost5:8],
               local2:[ghost4]memblock(W, 0, 8, fieldsh(int64<>)), local1:true,
               ghost4:true, ghost5:true


  Could not prove lifetime is current: ghost4"%string))) tt).

Definition use_mux_mut_refs : @CompM.lrtToType (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) :=
  SAWCoreScaffolding.fst (@use_mux_mut_refs__tuple_fun).

End rust_lifetimes.
