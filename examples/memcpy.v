
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module memcpy.

Definition mallocSpec : forall (sz : @SAWCorePrelude.bitvector 64), CompM (@SAWCorePrelude.BVVec 64 sz unit) :=
  fun (sz : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => @returnM CompM _ (@SAWCorePrelude.BVVec 64 sz unit) (@SAWCorePrelude.genBVVec 64 sz unit (fun (i : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (_1 : @SAWCoreScaffolding.EqP (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvult 64 i sz) (@SAWCoreScaffolding.true)) => tt)).

Definition llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64 : forall (e0 : Type), forall (e1 : @SAWCorePrelude.bitvector 64), forall (p0 : e0), forall (p1 : unit), CompM (prod unit (prod unit unit)) :=
  fun (X : Type) (len : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (x : X) (_1 : unit) => @returnM CompM _ (prod unit (prod unit unit)) (pair tt (pair tt tt)).

Definition copy_ptr_contents__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (@CompM.LRT_Nil)) (fun (copy_ptr_contents : @CompM.lrtToType (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))))) => pair (fun (p0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) tt (@errorM CompM _ (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) "At memcpy.c:13:3 ($12 = call $7($3, $5, $9, $11);)
  Regs: $7 = x11, $3 = x6, $5 = x9, $9 = x13, $11 = x15
  Input perms: top1:int64<>
  ,ghost3:llvmframe [x6:8, x5:8]
  ,x11:(z21, z20, z19, z18, z17, z16). arg26:[z20]memblock(W, 0,
                                                           z16, z18)
         ,arg25:[z19]memblock(z21, 0, z16, eqshz17)
         ,arg24:eq(LLVMword z16)
         ,arg23:true -o arg26:[z20]memblock(W, 0, z16, eqshz17)
         ,arg25:[z19]memblock(z21, 0, z16, eqshz17)
         ,arg24:true
         ,arg23:true
         ,ret22:true
  ,x6:ptr((W,0) |-> true)
  ,x9:eq(top1)
  ,x13:eq(LLVMword x4)
  ,x15:eq(LLVMword x14)
  ,x4:eq(8)
  ,x5:ptr((W,0) |-> eq(x9))
  ,x14:eq(0)
  Could not prove (z21, z20, z19, z18, z17, z16).
                    x6:[z20]memblock(W, 0, z16, z18)
                    ,x9:[z19]memblock(z21, 0, z16, eqshz17)
                    ,x13:eq(LLVMword z16)
                    ,x15:true

  proveVarLLVMBlock: Could not prove
  x6:ptr((W,0) |-> true)
  -o
  (z21, z20, z19, z18, z17, z16). [z20]memblock(W, 0, z16, z18)"%string)) tt).

Definition copy_ptr_contents : @CompM.lrtToType (@CompM.LRT_Fun (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) (fun (perm0 : @sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) :=
  SAWCoreScaffolding.fst (@copy_ptr_contents__tuple_fun).

End memcpy.
