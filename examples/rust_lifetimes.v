
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

Definition mkInt1Trans : @SAWCorePrelude.bitvector 1 -> int1Trans :=
  fun (bv : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => @existT (@SAWCorePrelude.bitvector 1) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit) bv tt.

Definition unInt1Trans : int1Trans -> @SAWCorePrelude.bitvector 1 :=
  fun (bv : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit)) => @projT1 (@SAWCorePrelude.bitvector 1) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit) bv.

Definition int8Trans : Type :=
  @sigT (@SAWCorePrelude.bitvector 8) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool)) => unit).

Definition int64Trans : Type :=
  @sigT (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit).

Definition mkInt64Trans : @SAWCorePrelude.bitvector 64 -> int64Trans :=
  fun (bv : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @existT (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) bv tt.

Definition unInt64Trans : int64Trans -> @SAWCorePrelude.bitvector 64 :=
  fun (bv : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) => @projT1 (@SAWCorePrelude.bitvector 64) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) bv.

Definition unfoldListPermH : forall (a : Type), @Datatypes.list a -> @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) :=
  fun (a : Type) (l : @Datatypes.list a) => @Datatypes.list_rect a (fun (_1 : @Datatypes.list a) => @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) (@SAWCorePrelude.Left unit (prod unit (prod a (@Datatypes.list a))) tt) (fun (x : a) (l1 : @Datatypes.list a) (_1 : @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) => @SAWCorePrelude.Right unit (prod unit (prod a (@Datatypes.list a))) (pair tt (pair x l1))) l.

Definition foldListPermH : forall (a : Type), @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) -> @Datatypes.list a :=
  fun (a : Type) => @SAWCorePrelude.either unit (prod unit (prod a (@Datatypes.list a))) (@Datatypes.list a) (fun (_1 : unit) => @Datatypes.nil a) (fun (tup : prod unit (prod a (@Datatypes.list a))) => @Datatypes.cons a (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd tup)) (SAWCoreScaffolding.snd (SAWCoreScaffolding.snd tup))).

Definition llvm__x2euadd__x2ewith__x2eoverflow__x2ei64 : forall (p0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)), forall (p1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @SAWCorePrelude.bitvector 1 in
  CompM (prod (@sigT var__0 (fun (x_ex0 : var__0) => unit)) (prod (@sigT var__1 (fun (x_ex0 : var__1) => unit)) unit)) :=
  fun (x : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) (y : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) => @returnM CompM _ (prod int64Trans (prod int1Trans unit)) (pair (@mkInt64Trans (@SAWCoreVectorsAsCoqVectors.bvAdd 64 (@unInt64Trans x) (@unInt64Trans y))) (pair (@mkInt1Trans (@SAWCoreVectorsAsCoqVectors.gen 1 (@SAWCoreScaffolding.Bool) (fun (_1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.bvCarry 64 (@unInt64Trans x) (@unInt64Trans y)))) tt)).

Definition llvm__x2eexpect__x2ei1 : forall (p0 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)), forall (p1 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)), let var__0   := @SAWCorePrelude.bitvector 1 in
  CompM (@sigT var__0 (fun (x_ex0 : var__0) => unit)) :=
  fun (x : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit)) (y : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 1 (@SAWCoreScaffolding.Bool)) => unit)) => @returnM CompM _ int1Trans x.

Definition mux_mut_refs_u64__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (fun (perm0 : forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm3 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit))))))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (fun (perm0 : forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm3 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit))))))) (@CompM.LRT_Nil)) (fun (mux_mut_refs_u64 : @CompM.lrtToType (@CompM.LRT_Fun (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (fun (perm0 : forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm3 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)))))))) => pair (fun (p0 : forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (p1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (p2 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (p3 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.letRecM (@CompM.LRT_Nil) (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) tt (if @SAWCoreScaffolding.not (@SAWCorePrelude.bvEq 1 (@projT1 (@SAWCorePrelude.bitvector 1) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 1) => unit) p3) (intToBv 1 0%Z)) then @errorM CompM _ (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) "At internal (return $1)
  Regs: $1 = x11
  Input perms: top1:lowned (top5:[top1]memblock(R, 0, 8,
                                                fieldsh(int64<>)),
                            top4:[top1]memblock(R, 0, 8, fieldsh(int64<>))
                            -o
                            top5:[top3]memblock(W, 0, 8, fieldsh(int64<>)),
                            top4:[top2]memblock(W, 0, 8, fieldsh(int64<>))),
               top2:true, top3:true, top4:[top1]memblock(W, 0, 8,
                                                         fieldsh(int64<>)),
               top5:[top1]memblock(W, 0, 8, fieldsh(int64<>)),
               top6:eq(LLVMword ghost9), x11:eq(top4), ghost9:true
  Could not prove: top1:lowned (x11:[top1]memblock(R, 0, 8,
                                                   fieldsh(int64<>))
                                -o
                                top5:[top3]memblock(W, 0, 8, fieldsh(int64<>)),
                                top4:[top2]memblock(W, 0, 8, fieldsh(int64<>))),
                   top2:true, top3:true, top4:true, top5:true, top6:true,
                   x11:[top1]memblock(W, 0, 8, fieldsh(int64<>))

  proveVarAtomicImpl: Could not prove
  top4:true -o (). [top1]ptr((R,0) |-> int64<>)"%string else @errorM CompM _ (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) "At internal (return $1)
  Regs: $1 = x11
  Input perms: top1:lowned (top5:[top1]memblock(R, 0, 8,
                                                fieldsh(int64<>)),
                            top4:[top1]memblock(R, 0, 8, fieldsh(int64<>))
                            -o
                            top5:[top3]memblock(W, 0, 8, fieldsh(int64<>)),
                            top4:[top2]memblock(W, 0, 8, fieldsh(int64<>))),
               top2:true, top3:true, top4:[top1]memblock(W, 0, 8,
                                                         fieldsh(int64<>)),
               top5:[top1]memblock(W, 0, 8, fieldsh(int64<>)),
               top6:eq(LLVMword ghost9), x11:eq(top5), ghost9:true
  Could not prove: top1:lowned (x11:[top1]memblock(R, 0, 8,
                                                   fieldsh(int64<>))
                                -o
                                top5:[top3]memblock(W, 0, 8, fieldsh(int64<>)),
                                top4:[top2]memblock(W, 0, 8, fieldsh(int64<>))),
                   top2:true, top3:true, top4:true, top5:true, top6:true,
                   x11:[top1]memblock(W, 0, 8, fieldsh(int64<>))

  proveVarAtomicImpl: Could not prove
  top5:true -o (). [top1]ptr((R,0) |-> int64<>)"%string)) tt).

Definition mux_mut_refs_u64 : @CompM.lrtToType (@CompM.LRT_Fun (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (fun (perm0 : forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm1 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm2 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (fun (perm3 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => @CompM.LRT_Ret (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit))))))) :=
  SAWCoreScaffolding.fst mux_mut_refs_u64__tuple_fun.

Definition use_mux_mut_refs__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (@CompM.LRT_Nil)) (fun (use_mux_mut_refs : @CompM.lrtToType (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => pair (@CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) tt (@bindM CompM _ (prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@mux_mut_refs_u64 (@SAWCorePrelude.composeM (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (fun (x_local0 : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) => @returnM CompM _ (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (pair (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd x_local0)) (pair (SAWCoreScaffolding.fst x_local0) tt))) (@SAWCorePrelude.composeM (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (@SAWCorePrelude.tupleCompMFunBoth (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@SAWCorePrelude.tupleCompMFunBoth unit unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (ps_empty : unit) => @returnM CompM _ unit ps_empty))) (fun (x_local0 : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) => @returnM CompM _ (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (pair (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd x_local0)) (pair (SAWCoreScaffolding.fst x_local0) tt))))) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 5%Z) tt) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 0x2a%Z) tt) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (intToBv 1 (-1)%Z) tt)) (fun (call_ret_val : prod (forall (ps : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit), let var__0   := @SAWCorePrelude.bitvector 64 in
  let var__1   := @sigT var__0 (fun (x_ex0 : var__0) => unit) in
  CompM (prod var__1 (prod var__1 unit))) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) => @bindM CompM _ (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@llvm__x2euadd__x2ewith__x2eoverflow__x2ei64 (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd call_ret_val)) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 1%Z) tt)) (fun (call_ret_val1 : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) unit)) => @bindM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@llvm__x2eexpect__x2ei1 (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd call_ret_val1)) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (intToBv 1 0%Z) tt)) (fun (call_ret_val2 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => if @SAWCoreScaffolding.not (@SAWCorePrelude.bvEq 1 (@projT1 (@SAWCorePrelude.bitvector 1) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 1) => unit) call_ret_val2) (intToBv 1 0%Z)) then @errorM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) "At internal ($0 = resolveGlobal llvm_memory ""_ZN4core9panicking5panic17hfb3ef93dcafb964cE"")
  Regs: 
  Input perms: ghost1:llvmframe [ghost2:8, ghost3:8], ghost2:true,
               ghost3:true
  Type-checking failure:
  LLVM_ResolveGlobal: no perms for global _ZN4core9panicking5panic17hfb3ef93dcafb964cE

  "%string else @bindM CompM _ (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (SAWCoreScaffolding.fst call_ret_val (pair (SAWCoreScaffolding.fst call_ret_val1) tt)) (fun (endl_ps0 : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) => @bindM CompM _ (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@llvm__x2euadd__x2ewith__x2eoverflow__x2ei64 (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd endl_ps0)) (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (intToBv 64 1%Z) tt)) (fun (call_ret_val3 : prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (prod (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) unit)) => @bindM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@llvm__x2eexpect__x2ei1 (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd call_ret_val3)) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (intToBv 1 0%Z) tt)) (fun (call_ret_val4 : @sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) => if @SAWCoreScaffolding.not (@SAWCorePrelude.bvEq 1 (@projT1 (@SAWCorePrelude.bitvector 1) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 1) => unit) call_ret_val4) (intToBv 1 0%Z)) then @errorM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) "At internal ($0 = resolveGlobal llvm_memory ""_ZN4core9panicking5panic17hfb3ef93dcafb964cE"")
  Regs: 
  Input perms: ghost1:llvmframe [ghost2:8, ghost5:8],
               ghost2:memblock(W, 8, 0, emptysh)*ptr((W,0) |-> eq(ghost3)),
               ghost5:memblock(W, 0, 8, fieldsh(int64<>)), ghost3:eq(ghost4),
               ghost4:int64<>
  Type-checking failure:
  LLVM_ResolveGlobal: no perms for global _ZN4core9panicking5panic17hfb3ef93dcafb964cE

  "%string else @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (SAWCoreScaffolding.fst call_ret_val3))))))))) tt).

Definition use_mux_mut_refs : @CompM.lrtToType (@CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) :=
  SAWCoreScaffolding.fst use_mux_mut_refs__tuple_fun.

End rust_lifetimes.
