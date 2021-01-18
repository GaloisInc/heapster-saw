
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module rust_data.

Definition unfoldListPermH : forall (a : Type), @Datatypes.list a -> @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) :=
  fun (a : Type) (l : @Datatypes.list a) => @Datatypes.list_rect a (fun (_1 : @Datatypes.list a) => @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) (@SAWCorePrelude.Left unit (prod unit (prod a (@Datatypes.list a))) tt) (fun (x : a) (l1 : @Datatypes.list a) (_1 : @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a)))) => @SAWCorePrelude.Right unit (prod unit (prod a (@Datatypes.list a))) (pair tt (pair x l1))) l.

Definition foldListPermH : forall (a : Type), @SAWCorePrelude.Either unit (prod unit (prod a (@Datatypes.list a))) -> @Datatypes.list a :=
  fun (a : Type) => @SAWCorePrelude.either unit (prod unit (prod a (@Datatypes.list a))) (@Datatypes.list a) (fun (_1 : unit) => @Datatypes.nil a) (fun (tup : prod unit (prod a (@Datatypes.list a))) => @Datatypes.cons a (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd tup)) (SAWCoreScaffolding.snd (SAWCoreScaffolding.snd tup))).

Definition ListPerm : forall (e0 : Type), forall (e1 : @SAWCorePrelude.bitvector 64), Type :=
  fun (X : Type) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @Datatypes.list X.

Definition foldListPerm : forall (e0 : Type), forall (e1 : @SAWCorePrelude.bitvector 64), forall (p0 : @SAWCorePrelude.Either unit (prod unit (prod e0 (@ListPerm e0 e1)))), @ListPerm e0 e1 :=
  fun (X : Type) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @foldListPermH X.

Definition unfoldListPerm : forall (e0 : Type), forall (e1 : @SAWCorePrelude.bitvector 64), forall (p0 : @ListPerm e0 e1), @SAWCorePrelude.Either unit (prod unit (prod e0 (@ListPerm e0 e1))) :=
  fun (X : Type) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @unfoldListPermH X.

Definition exchange_malloc : forall (e0 : @SAWCorePrelude.bitvector 64), CompM (@SAWCorePrelude.BVVec 64 e0 unit) :=
  fun (len : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @returnM CompM _ (@SAWCorePrelude.BVVec 64 len unit) (@SAWCorePrelude.repeatBVVec 64 len unit tt).

Definition test_result__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) (fun (test_result : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit))))) => pair (fun (p0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) tt (@SAWCorePrelude.either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (CompM (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit))) (fun (x_left0 : prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) => @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (@SAWCorePrelude.bvTrunc 7 1 (intToBv 8 1%Z)) tt)) (fun (x_right0 : prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) => @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (@SAWCorePrelude.bvTrunc 7 1 (intToBv 8 0%Z)) tt)) p0)) tt).

Definition test_result : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) :=
  SAWCoreScaffolding.fst (@test_result__tuple_fun).

Definition test_sum_impl__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) (fun (test_sum_impl : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit))))) => pair (fun (p0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) tt (@errorM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) "At internal ($3 = load llvm_memory $0 bitvectorType 8 Alignment 3)
  Regs: $0 = local2
  Input perms: top1:memblock(R, 0, 0, ptrsh(eq(LLVMword 0));
                                 ptrsh(int64<>) orsh
                               ptrsh(eq(LLVMword 1)); ptrsh(int64<>))
  ,ghost3:llvmframe [x5:1]
  ,local2:eq(top1)
  ,x5:ptr((W,0,8) |-> true)
  Could not prove (z8, z7, z6). local2:[z7]ptr((z8,0) |-> eq(z6))

  proveVarAtomicImpl: Could not prove
  top1:memblock(R, 0, 0, ptrsh(eq(LLVMword 0));
                    ptrsh(int64<>) orsh
                  ptrsh(eq(LLVMword 1)); ptrsh(int64<>))
  -o
  (z8, z7, z6). [z7]ptr((z8,0) |-> eq(z6))"%string)) tt).

Definition test_sum_impl : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) :=
  SAWCoreScaffolding.fst (@test_sum_impl__tuple_fun).

Definition list_is_empty__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) (fun (list_is_empty : @CompM.lrtToType (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit))))) => pair (fun (p0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) tt (@SAWCorePrelude.either unit (prod unit (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)))) (CompM (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit))) (fun (x_left0 : unit) => @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (@SAWCorePrelude.bvTrunc 7 1 (intToBv 8 1%Z)) tt)) (fun (x_right0 : prod unit (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)))) => @returnM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) (@existT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit) (@SAWCorePrelude.bvTrunc 7 1 (intToBv 8 0%Z)) tt)) (@unfoldListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z) p0))) tt).

Definition list_is_empty : @CompM.lrtToType (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) :=
  SAWCoreScaffolding.fst (@list_is_empty__tuple_fun).

Definition list_head__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)))) (@CompM.LRT_Nil)) (fun (list_head : @CompM.lrtToType (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))))) => pair (fun (p0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.letRecM (@CompM.LRT_Nil) (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) tt (@SAWCorePrelude.either unit (prod unit (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)))) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (fun (x_left0 : unit) => @bindM CompM _ (@SAWCorePrelude.BVVec 64 (intToBv 64 0x10%Z) unit) (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) (@exchange_malloc (intToBv 64 0x10%Z)) (fun (call_ret_val : @SAWCorePrelude.BVVec 64 (intToBv 64 0x10%Z) unit) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 0%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "0 <=u 16"%string) (fun (ule_pf0 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 0%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 0%Z))) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 16 - 0"%string) (fun (ule_diff_pf0 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 0%Z))) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 16"%string) (fun (ule_pf1 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 8%Z))) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 16 - 8"%string) (fun (ule_diff_pf1 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 8%Z))) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 8%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 8"%string) (fun (ule_pf2 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 8%Z)) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 (-8)%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 18446744073709551608"%string) (fun (ule_pf3 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 (-8)%Z)) (@SAWCoreScaffolding.true)) => @returnM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) (@SAWCorePrelude.Right (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit) (pair tt tt))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (intToBv 64 (-8)%Z))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (intToBv 64 8%Z))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 8%Z)))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (intToBv 64 0x10%Z))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 0%Z)))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 0%Z) (intToBv 64 0x10%Z)))) (fun (x_right0 : prod unit (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)))) => @bindM CompM _ (@SAWCorePrelude.BVVec 64 (intToBv 64 0x10%Z) unit) (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) (@exchange_malloc (intToBv 64 0x10%Z)) (fun (call_ret_val : @SAWCorePrelude.BVVec 64 (intToBv 64 0x10%Z) unit) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 0%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "0 <=u 16"%string) (fun (ule_pf0 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 0%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 0%Z))) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 16 - 0"%string) (fun (ule_diff_pf0 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 0%Z))) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 16"%string) (fun (ule_pf1 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 0x10%Z)) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 8%Z))) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 16 - 8"%string) (fun (ule_diff_pf1 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 8%Z))) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 8%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 8"%string) (fun (ule_pf2 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 8%Z)) (@SAWCoreScaffolding.true)) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 (-8)%Z)) (@SAWCoreScaffolding.true)) (CompM (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit))) (@errorM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) "8 <=u 18446744073709551608"%string) (fun (ule_pf3 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvule 64 (intToBv 64 8%Z) (intToBv 64 (-8)%Z)) (@SAWCoreScaffolding.true)) => @returnM CompM _ (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)) (@SAWCorePrelude.Left (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit) (pair tt (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd x_right0))))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (intToBv 64 (-8)%Z))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (intToBv 64 8%Z))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 8%Z)))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (intToBv 64 0x10%Z))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 8%Z) (@SAWCoreVectorsAsCoqVectors.bvSub 64 (intToBv 64 0x10%Z) (intToBv 64 0%Z)))) (@SAWCorePrelude.bvuleWithProof 64 (intToBv 64 0%Z) (intToBv 64 0x10%Z)))) (@unfoldListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z) p0))) tt).

Definition list_head : @CompM.lrtToType (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit unit)))) :=
  SAWCoreScaffolding.fst (@list_head__tuple_fun).

Definition list_head_impl__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit))) (@CompM.LRT_Nil)) (fun (list_head_impl : @CompM.lrtToType (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)))) => pair (fun (p0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.letRecM (@CompM.LRT_Nil) (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit) tt (@SAWCorePrelude.either unit (prod unit (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)))) (CompM (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit)) (fun (x_left0 : unit) => @returnM CompM _ (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit) (@SAWCorePrelude.Right (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit tt)) (fun (x_right0 : prod unit (prod (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)))) => @returnM CompM _ (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit) (@SAWCorePrelude.Left (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit (@existT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit) (@projT1 (@SAWCorePrelude.bitvector 64) (fun (x_elimEx0 : @SAWCorePrelude.bitvector 64) => unit) (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd x_right0))) tt))) (@unfoldListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z) p0))) tt).

Definition list_head_impl : @CompM.lrtToType (@CompM.LRT_Fun (@ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) (fun (perm0 : @ListPerm (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (intToBv 64 8%Z)) => @CompM.LRT_Ret (@SAWCorePrelude.Either (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) unit))) :=
  SAWCoreScaffolding.fst (@list_head_impl__tuple_fun).

End rust_data.
