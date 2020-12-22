
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module rust_data.

Definition test_result__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) (@CompM.LRT_Nil)) (fun (test_result : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit))))) => pair (fun (p0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.letRecM (@CompM.LRT_Nil) (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) tt (@errorM CompM _ (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)) "At internal ($11 = extensionApp(pointerBlock $10))
  Regs: $10 = x17
  Input perms: top1:true
  ,top2:memblock(top1, 0, 16, ptrsh((eq(LLVMword 0)));
                     ptrsh((int64<>)) orsh
                   ptrsh((eq(LLVMword 1))); ptrsh((int64<>)))
  ,top3:true
  ,ghost6:llvmframe [x10:16, x8:1]
  ,x17:eq(top2)
  ,x8:ptr((W,0,8) |-> true)
  ,x10:ptr((W,8) |-> eq(local5))*ptr((W,0) |-> eq(x17))
  ,local5:eq(top3)
  Could not prove (). x17:is_llvmptr

  proveVarAtomicImpl: Could not prove
  top2:memblock(top1, 0, 16, ptrsh((eq(LLVMword 0)));
                    ptrsh((int64<>)) orsh
                  ptrsh((eq(LLVMword 1))); ptrsh((int64<>)))
  -o
  (). is_llvmptr"%string)) tt).

Definition test_result : @CompM.lrtToType (@CompM.LRT_Fun (@SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) (fun (perm0 : @SAWCorePrelude.Either (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit))) (prod unit (@sigT (@SAWCorePrelude.bitvector 64) (fun (x_ex0 : @SAWCorePrelude.bitvector 64) => unit)))) => @CompM.LRT_Ret (@sigT (@SAWCorePrelude.bitvector 1) (fun (x_ex0 : @SAWCorePrelude.bitvector 1) => unit)))) :=
  SAWCoreScaffolding.fst (@test_result__tuple_fun).

End rust_data.
