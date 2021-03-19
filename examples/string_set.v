
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.

Import ListNotations.

Module StringSet.

Definition listInsertM : forall (a : Type), @Datatypes.list a -> a -> CompM (@Datatypes.list a) :=
  fun (a : Type) (l : @Datatypes.list a) (s : a) => @returnM CompM _ (@Datatypes.list a) (@Datatypes.cons a s l).

Definition listRemoveM : forall (a : Type), (a -> a -> @SAWCoreScaffolding.Bool) -> @Datatypes.list a -> a -> CompM (prod (@Datatypes.list a) (prod a unit)) :=
  fun (a : Type) (test_eq : a -> a -> @SAWCoreScaffolding.Bool) (l : @Datatypes.list a) (s : a) => @returnM CompM _ (prod (@Datatypes.list a) (prod a unit)) (pair (@Datatypes.list_rect a (fun (_1 : @Datatypes.list a) => @Datatypes.list a) (@Datatypes.nil a) (fun (s' : a) (_1 : @Datatypes.list a) (rec : @Datatypes.list a) => if test_eq s s' then rec else @Datatypes.cons a s' rec) l) (pair s tt)).

Definition stringList : Type :=
  @Datatypes.list (@SAWCoreScaffolding.String).

Definition stringListInsertM : @Datatypes.list (@SAWCoreScaffolding.String) -> @SAWCoreScaffolding.String -> CompM (@Datatypes.list (@SAWCoreScaffolding.String)) :=
  fun (l : @Datatypes.list (@SAWCoreScaffolding.String)) (s : @SAWCoreScaffolding.String) => @returnM CompM _ (@Datatypes.list (@SAWCoreScaffolding.String)) (@Datatypes.cons (@SAWCoreScaffolding.String) s l).

Definition stringListRemoveM : @Datatypes.list (@SAWCoreScaffolding.String) -> @SAWCoreScaffolding.String -> CompM (prod stringList (prod (@SAWCoreScaffolding.String) unit)) :=
  fun (l : @Datatypes.list (@SAWCoreScaffolding.String)) (s : @SAWCoreScaffolding.String) => @returnM CompM _ (prod stringList (prod (@SAWCoreScaffolding.String) unit)) (pair (@Datatypes.list_rect (@SAWCoreScaffolding.String) (fun (_1 : @Datatypes.list (@SAWCoreScaffolding.String)) => @Datatypes.list (@SAWCoreScaffolding.String)) (@Datatypes.nil (@SAWCoreScaffolding.String)) (fun (s' : @SAWCoreScaffolding.String) (_1 : @Datatypes.list (@SAWCoreScaffolding.String)) (rec : @Datatypes.list (@SAWCoreScaffolding.String)) => if @SAWCoreScaffolding.equalString s s' then rec else @Datatypes.cons (@SAWCoreScaffolding.String) s' rec) l) (pair s tt)).

Definition string : Type :=
  @SAWCoreScaffolding.String.

Definition string_set : Type :=
  @Datatypes.list (@SAWCoreScaffolding.String).

Definition string_set_insert : forall (p0 : string_set), forall (p1 : string), CompM string_set :=
  @listInsertM (@SAWCoreScaffolding.String).

Definition string_set_remove : forall (p0 : string_set), forall (p1 : string), CompM (prod string_set (prod string unit)) :=
  @listRemoveM (@SAWCoreScaffolding.String) (@SAWCoreScaffolding.equalString).

Definition insert_remove__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun string_set (fun (perm0 : string_set) => @CompM.LRT_Fun string (fun (perm1 : string) => @CompM.LRT_Fun string (fun (perm2 : string) => @CompM.LRT_Ret (prod string_set (prod string unit)))))) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun string_set (fun (perm0 : string_set) => @CompM.LRT_Fun string (fun (perm1 : string) => @CompM.LRT_Fun string (fun (perm2 : string) => @CompM.LRT_Ret (prod string_set (prod string unit)))))) (@CompM.LRT_Nil)) (fun (insert_remove : @CompM.lrtToType (@CompM.LRT_Fun string_set (fun (perm0 : string_set) => @CompM.LRT_Fun string (fun (perm1 : string) => @CompM.LRT_Fun string (fun (perm2 : string) => @CompM.LRT_Ret (prod string_set (prod string unit))))))) => pair (fun (p0 : string_set) (p1 : string) (p2 : string) => @CompM.letRecM (@CompM.LRT_Nil) (prod string_set (prod string unit)) tt (@errorM CompM _ (prod string_set (prod string unit)) "At string_set.c:15:3 ($14 = call $13($10, $11);)
  Regs: $13 = x22, $10 = x19, $11 = x20
  Input perms: top1:true, top2:string_set<W, top1>, top3:string<>,
               top4:string<>, ghost8:llvmframe [x12:8, x11:8, x10:8],
               x22:(ghost26:lifetime).
                   ghost26:true, arg25:string_set<W, ghost26>, arg24:string<>
                   -o
                   ghost26:true, arg25:string_set<W, ghost26>, arg24:true,
                   ret23:true, x19:eq(top2), x20:eq(top3), x10:ptr((W,0) |->
                                                                     eq(x19)),
               x11:ptr((W,0) |-> eq(x20)), x12:ptr((W,0) |-> eq(local7)),
               local7:eq(top4)
  Could not prove (z23). z23:true, x19:string_set<W, z23>,
                         x20:string<>

  Could not determine enough variables to prove permissions:
  (z23). z23:true, x19:string_set<W, z23>"%string)) tt).

Definition insert_remove : @CompM.lrtToType (@CompM.LRT_Fun string_set (fun (perm0 : string_set) => @CompM.LRT_Fun string (fun (perm1 : string) => @CompM.LRT_Fun string (fun (perm2 : string) => @CompM.LRT_Ret (prod string_set (prod string unit)))))) :=
  SAWCoreScaffolding.fst insert_remove__tuple_fun.

End StringSet.
