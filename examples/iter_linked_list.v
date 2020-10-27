
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module iter_linked_list.

Inductive ListF (a : Type) (b : Type) : Type :=
| NilF : (b) -> ((@ListF) (a) (b))
| ConsF : (a) -> (((@ListF) (a) (b))) -> ((@ListF) (a) (b))
.

Definition ListF_def : forall (a : Type), forall (b : Type), Type :=
  (fun (a : Type) (b : Type) => ((@ListF) (a) (b))).

Definition ListF__rec : forall (a : Type), forall (b : Type), forall (P : (((@ListF) (a) (b))) -> Type), (forall (x : b), ((P) (((@NilF) (a) (b) (x))))) -> (forall (x : a), forall (l : ((@ListF) (a) (b))), (((P) (l))) -> ((P) (((@ConsF) (a) (b) (x) (l))))) -> forall (l : ((@ListF) (a) (b))), ((P) (l)) :=
  (fun (a : Type) (b : Type) (P : (((@ListF) (a) (b))) -> Type) (f1 : forall (x : b), ((P) (((@NilF) (a) (b) (x))))) (f2 : forall (x : a), forall (l : ((@ListF) (a) (b))), (((P) (l))) -> ((P) (((@ConsF) (a) (b) (x) (l))))) (l : ((@ListF) (a) (b))) => ((iter_linked_list.ListF_rect) (a) (b) (P) (f1) (f2) (l))).

Definition unfoldListF : forall (a : Type), forall (b : Type), (((@ListF) (a) (b))) -> ((@SAWCorePrelude.Either) (b) (((prod) (a) (((prod) (((@ListF) (a) (b))) (unit)))))) :=
  (fun (a : Type) (b : Type) (l : ((@ListF) (a) (b))) => ((@ListF__rec) (a) (b) ((fun (_ : ((@ListF) (a) (b))) => ((@SAWCorePrelude.Either) (b) (((prod) (a) (((prod) (((@ListF) (a) (b))) (unit)))))))) ((fun (x : b) => ((@SAWCorePrelude.Left) (b) (((prod) (a) (((prod) (((@ListF) (a) (b))) (unit))))) (x)))) ((fun (x : a) (l_0 : ((@ListF) (a) (b))) (_ : ((@SAWCorePrelude.Either) (b) (((prod) (a) (((prod) (((@ListF) (a) (b))) (unit))))))) => ((@SAWCorePrelude.Right) (b) (((prod) (a) (((prod) (((@ListF) (a) (b))) (unit))))) (((pair) (x) (((pair) (l_0) (tt)))))))) (l))).

Definition foldListF : forall (a : Type), forall (b : Type), (((@SAWCorePrelude.Either) (b) (((prod) (a) (((prod) (((@ListF) (a) (b))) (unit))))))) -> ((@ListF) (a) (b)) :=
  (fun (a : Type) (b : Type) => ((@SAWCorePrelude.either) (b) (((prod) (a) (((prod) (((@ListF) (a) (b))) (unit))))) (((@ListF) (a) (b))) ((fun (x : b) => ((@NilF) (a) (b) (x)))) ((fun (tup : ((prod) (a) (((prod) (((@ListF) (a) (b))) (unit))))) => ((@ConsF) (a) (b) (((SAWCoreScaffolding.fst) (tup))) (((SAWCoreScaffolding.fst) (((SAWCoreScaffolding.snd) (tup)))))))))).

Definition getListF : forall (a : Type), forall (b : Type), (((@ListF) (a) (b))) -> b :=
  (fun (a : Type) (b : Type) => ((@ListF__rec) (a) (b) ((fun (_ : ((@ListF) (a) (b))) => b)) ((fun (x : b) => x)) ((fun (_ : a) (__0 : ((@ListF) (a) (b))) (rec : b) => rec)))).

Definition putListF : forall (a : Type), forall (b : Type), forall (c : Type), (((@ListF) (a) (b))) -> (c) -> ((@ListF) (a) (c)) :=
  (fun (a : Type) (b : Type) (c : Type) (l : ((@ListF) (a) (b))) (c_val : c) => ((@ListF__rec) (a) (b) ((fun (_ : ((@ListF) (a) (b))) => ((@ListF) (a) (c)))) ((fun (_ : b) => ((@NilF) (a) (c) (c_val)))) ((fun (x : a) (_ : ((@ListF) (a) (b))) (rec : ((@ListF) (a) (c))) => ((@ConsF) (a) (c) (x) (rec)))) (l))).

Definition transListF : forall (a : Type), forall (b : Type), (((@ListF) (a) (unit))) -> (((@ListF) (a) (b))) -> ((@ListF) (a) (b)) :=
  (fun (a : Type) (b : Type) (l1 : ((@ListF) (a) (unit))) (l2 : ((@ListF) (a) (b))) => ((@ListF__rec) (a) (unit) ((fun (_ : ((@ListF) (a) (unit))) => ((@ListF) (a) (b)))) ((fun (_ : unit) => l2)) ((fun (x : a) (_ : ((@ListF) (a) (unit))) (rec : ((@ListF) (a) (b))) => ((@ConsF) (a) (b) (x) (rec)))) (l1))).

Definition incr_list__tuple_fun : ((@CompM.lrtTupleType) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (perm0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Ret) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit)))))))) (((@CompM.LRT_Nil)))))) :=
  ((@CompM.multiFixM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (perm0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Ret) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit)))))))) (((@CompM.LRT_Nil))))) ((fun (incr_list : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (perm0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Ret) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit)))))))))) => ((pair) ((fun (p0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.letRecM) (((@CompM.LRT_Cons) (((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (p0_0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (p1 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Ret) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))))))))) (((@CompM.LRT_Nil))))) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (f : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (p0_0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (p1 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Ret) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))))))))))) => ((pair) ((fun (p0_0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) (p1 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@SAWCorePrelude.either) (unit) (((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) (unit))))) (((CompM) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))) ((fun (x_left0 : unit) => ((((@errorM) (CompM) (_))) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) (("At iter_linked_list.c:22:1 (return $1)
  Regs: $1 = x6
  Input perms: top1:true,x6:true
  Could not prove: top1:ListF<exists z7. eq(LLVMword z7)
                              ,always
                              ,W
                              ,eq(LLVMword 0)>
                   ,x6:true
  
  proveVarEqH: Could not prove top1:true -o (). eq(LLVMword 0)
  
  --------------------
  
  proveVarAtomicImpl: Could not prove
  top1:true -o (). ptr((W,0) |-> exists z7. eq(LLVMword z7))")%string)))) ((fun (x_right0 : ((prod) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (((prod) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) (unit))))) => if ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvSCarry) (63) (((@projT1) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_elimEx0 : ((@SAWCorePrelude.bitvector) (64))) => unit)) (((SAWCoreScaffolding.fst) (x_right0))))) (((intToBv) (64) (1%Z)))))) then ((((@errorM) (CompM) (_))) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) (("At iter_linked_list.c:20:3 (jump %3($0))
  Regs: $0 = local2
  Input perms: top1:ListF<exists z15. eq(LLVMword z15)
                          ,always
                          ,W
                          ,eq(ghost5)>
               ,ghost3:llvmframe [local2:8]
               ,local2:ptr((W,0) |-> eq(x13))
               ,ghost5:ptr((W,0) |-> eq(ghost6))*ptr((W,8) |-> eq(x13))
               ,x13:eq(z12)
               ,ghost6:eq(LLVMword ghost7)
               ,z12:ListF<exists z15. eq(LLVMword z15),always,W,eq(LLVMword 0)>
               ,ghost7:eq(1*ghost8+1)
               ,ghost8:true
  Could not prove:  (z16,z15).
                      top1:ListF<exists z17. eq(LLVMword z17),always,W,eq(z15)>
                      ,local2:ptr((W,0) |-> eq(z15))
                      ,z16:llvmframe [local2:8]
                      ,z15:ListF<exists z17. eq(LLVMword z17)
                                 ,always
                                 ,W
                                 ,eq(LLVMword 0)>
  
  proveVarEqH: Could not prove
  ghost5:ptr((W,0) |-> eq(ghost6))*ptr((W,8) |-> eq(x13))
  -o
  (z16,z15). eq(z15)
  
  --------------------
  
  proveVarEqH: Could not prove
  z12:true -o (z17,z16). eq(LLVMword 0)
  
  --------------------
  
  proveVarImplH: Could not prove
  z15:eq(LLVMword 0)
  -o
  (z17,z16). ptr((W,0) |-> exists z18. eq(LLVMword z18))
             *ptr((W,8) |-> ListF<exists z18. eq(LLVMword z18)
                                  ,always
                                  ,W
                                  ,eq(z16)>)")%string)) else ((((@errorM) (CompM) (_))) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) (("Failed Assert at iter_linked_list.c:21:12")%string)))) (((@unfoldListF) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit) (p1)))))) (tt)))) ((fun (f : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (p0_0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (p1 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Ret) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))))))))))) => ((((@errorM) (CompM) (_))) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) (("At iter_linked_list.c:20:3 (jump %3($2))
  Regs: $2 = x5
  Input perms: top1:ListF<exists z8. eq(LLVMword z8)
                          ,always
                          ,W
                          ,eq(LLVMword 0)>
               ,ghost3:llvmframe [x5:8]
               ,x5:ptr((W,0) |-> eq(local2))
               ,local2:eq(top1)
  Could not prove:  (z9,z8).
                      top1:ListF<exists z10. eq(LLVMword z10),always,W,eq(z8)>
                      ,x5:ptr((W,0) |-> eq(z8))
                      ,z9:llvmframe [x5:8]
                      ,z8:ListF<exists z10. eq(LLVMword z10)
                                ,always
                                ,W
                                ,eq(LLVMword 0)>
  
  proveVarEqH: Could not prove
  top1:true -o (z10,z9). eq(LLVMword 0)
  
  --------------------
  
  proveVarImplH: Could not prove
  z8:eq(LLVMword 0)
  -o
  (z10,z9). ptr((W,0) |-> exists z11. eq(LLVMword z11))
            *ptr((W,8) |-> ListF<exists z11. eq(LLVMword z11)
                                 ,always
                                 ,W
                                 ,eq(z9)>)")%string))))))) (tt))))).

Definition incr_list : ((@CompM.lrtToType) (((@CompM.LRT_Fun) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) ((fun (perm0 : ((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))) => ((@CompM.LRT_Ret) (((@ListF_def) (((@sigT) (((@SAWCorePrelude.bitvector) (64))) ((fun (x_ex0 : ((@SAWCorePrelude.bitvector) (64))) => unit)))) (unit))))))))) :=
  ((SAWCoreScaffolding.fst) (((@incr_list__tuple_fun)))).

End iter_linked_list.
