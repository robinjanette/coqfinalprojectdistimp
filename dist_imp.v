(* Not heaps *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Maps.
Require Import Imp.
(*Require Import Smallstep.*)

Module DistIMP.

(*Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.*)

Definition sb := list (nat * id).

Definition rb := list nat.

Inductive State : Type :=
| state : sb  -> rb -> total_map nat -> State.

(*Definition empty_state : State := state [] [] (t_empty 0).*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* Distributed Commands*)
  | CSend : id -> aexp -> com
  | CRecieve: com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'SEND' a 'TO' id" :=
  (CSend id a) (at level  80, right associativity).
Notation "'RECIEVE'"  :=
  (CRecieve) (at level 80, right associativity).

Check state.

Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

(** We are not actually going to bother to define boolean
    values, since they aren't needed in the definition of [==>b]
    below (why?), though they might be if our language were a bit
    larger (why?). *)

Reserved Notation " t '/' st '==>a' t' " (at level 40, st at level 39).

Inductive astep : State -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st ==>a ANum (st i)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ==>a ANum (n1 + n2)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (APlus a1 a2) / st ==>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (APlus v1 a2) / st ==>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st ==>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMinus a1 a2) / st ==>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMinus v1 a2) / st ==>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st ==>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMult (a1) (a2)) / st ==>a (AMult (a1') (a2))
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMult v1 a2) / st ==>a (AMult v1 a2')

    where " t '/' st '==>a' t' " := (astep st t t').

  Reserved Notation " t '/' st '==>b' t' " (at level 40, st at level 39).

  Inductive bstep : State -> bexp -> bexp -> Prop :=
  | BS_Eq : forall st n1 n2,
      (BEq (ANum n1) (ANum n2)) / st ==>b
      (if (beq_nat n1 n2) then BTrue else BFalse)
  | BS_Eq1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (BEq a1 a2) / st ==>b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (BEq v1 a2) / st ==>b (BEq v1 a2')
  | BS_LtEq : forall st n1 n2,
      (BLe (ANum n1) (ANum n2)) / st ==>b
               (if (leb n1 n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (BLe a1 a2) / st ==>b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (BLe v1 a2) / st ==>b (BLe v1 (a2'))
  | BS_NotTrue : forall st,
      (BNot BTrue) / st ==>b BFalse
  | BS_NotFalse : forall st,
      (BNot BFalse) / st ==>b BTrue
  | BS_NotStep : forall st b1 b1',
      b1 / st ==>b b1' ->
      (BNot b1) / st ==>b (BNot b1')
  | BS_AndTrueTrue : forall st,
      (BAnd BTrue BTrue) / st ==>b BTrue
  | BS_AndTrueFalse : forall st,
      (BAnd BTrue BFalse) / st ==>b BFalse
  | BS_AndFalse : forall st b2,
      (BAnd BFalse b2) / st ==>b BFalse
  | BS_AndTrueStep : forall st b2 b2',
      b2 / st ==>b b2' ->
      (BAnd BTrue b2) / st ==>b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
      b1 / st ==>b b1' ->
      (BAnd b1 b2) / st ==>b (BAnd b1' b2)

  where " t '/' st '==>b' t' " := (bstep st t t').


Reserved Notation " t '/' st '==>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Check CSkip.

Inductive cstep : (com * State) -> (com * State) -> Prop :=
  (*| CS_AssStep : forall st i a a',
      a / st ==>a a' ->
      (i ::= a) / st ==> (i ::= a') / st*)
  (*| CS_Ass : forall sb rb (st : State) i n,
      (i ::= (ANum n)) / st ==> SKIP / state sb rb (t_update st i n)*)
  | CS_SeqStep : forall (st: State) (c1 c1': com) (st' : State) (c2 : com),
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st ==>b b' ->
          IFB b THEN c1 ELSE c2 FI / st 
      ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ==> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st.
  (*| CS_Send : 
      (SEND a TO id) / st -*)

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

End DistIMP.

