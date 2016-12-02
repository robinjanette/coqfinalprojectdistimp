(* Not heaps *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Maps.
Require Import Imp.
Require Import Coq.Lists.List.
Import List Notations.
Require Import Smallstep.

Module DistIMP.

Inductive aexp : Type :=
  | AId : id -> aexp
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
  | CSend : aexp -> id -> id -> com
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
Notation "'SEND' a 'TO' id1 'CALLED' id2" :=
  (CSend a id1 id2) (at level  80, right associativity).
Notation "'RECEIVE'"  :=
  (CRecieve) (at level 80, right associativity).

(*Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.*)

Inductive triple (A B C : Type) : Type :=
  | trip : A -> B -> C -> triple A B C.

Notation "x '*' y '*' z" := (triple x y z) 
  (at level 70, right associativity).

Definition sb := list (aexp * id * id).

Definition rb := list (aexp * id).

Definition st := total_map nat.

Inductive State : Type :=
| state : sb  -> rb -> st -> State.

Definition empty_state : State := state nil nil (t_empty 0).

Check state.

Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '==>a' t' " (at level 40, st at level 39).

Inductive astep : State -> aexp -> aexp -> Prop :=
  | AS_Id : forall sb rb st i,
      AId i / state sb rb st ==>a ANum (st i)
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

Inductive cstep : (com * State) -> (com * State) -> Prop :=
  | CS_AssStep : forall (sb1 : sb) (rb1 : rb) (st1 : st) (i : id) (a a' : aexp),
      a / state sb1 rb1 st1 ==>a a' ->
      cstep (i ::= a, state sb1 rb1 st1) (i ::= a', state sb1 rb1 st1)
  | CS_Ass : forall (sb1 : sb) (rb1 : rb) (st1 : st) (i : id) (n : nat),
      cstep (i ::= (ANum n), state sb1 rb1 st1) 
      (SKIP, state sb1 rb1 (t_update st1 i n))
  | CS_SeqSkip : forall (c2 : com) (st : State),
      cstep (SKIP ;; c2, st) (c2, st)
  | CS_SeqStep : forall (st: State) (c1 c1': com) (st' : State) (c2 : com),
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2, st) (c1' ;; c2, st')
  | CS_SeqFinish : forall (sb1 : sb) (rb1 : rb) (st1 : st) (c2 : com),
      cstep (SKIP ;; c2, state sb1 rb1 st1) (c2, state sb1 rb1 st1)
  | CS_IfTrue : forall (sb1 : sb) (rb1 : rb) (st1 : st) (c1 c2 : com),
      cstep (IFB BTrue THEN c1 ELSE c2 FI, state sb1 rb1 st1)
      (c1, state sb1 rb1 st1)
  | CS_IfFalse : forall (sb1 : sb) (rb1 : rb) (st1 : st) (c1 c2 : com),
      cstep (IFB BFalse THEN c1 ELSE c2 FI, state sb1 rb1 st1) 
      (c2, state sb1 rb1 st1)
  | CS_IfStep : forall (sb1 : sb) (rb1 : rb) (st1 : st)
                (b b' : bexp) (c1 c2: com),
      b / state sb1 rb1 st1 ==>b b' ->
      cstep (IFB b THEN c1 ELSE c2 FI, state sb1 rb1 st1) 
      ((IFB b' THEN c1 ELSE c2 FI), state sb1 rb1 st1)
  | CS_While : forall (sb1 : sb) (rb1 : rb) (st1 : st) (b : bexp) (c1 : com),
      cstep (WHILE b DO c1 END, state sb1 rb1 st1)
      ((IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI), state sb1 rb1 st1)

  | CS_Send1 : forall (sb1 : sb) (rb1 : rb)
                      (st1 : st) (a a' : aexp) (x z : id),
      a / state sb1 rb1 st1 ==>a a' -> 
      cstep (SEND a TO x CALLED z, state sb1 rb1 st1) 
            (SEND a' TO x CALLED z, state sb1 rb1 st1)
  | CS_Send2 : forall (sb1 : sb) (rb1 : rb) (st1 : st) 
                      (a : aexp) (x z : id) (n : nat),
      a = ANum n ->
      cstep (SEND a TO x CALLED z, state sb1 rb1 st1) 
            (SKIP, state (app sb1 (cons (a, x, z) nil)) rb1 st1)
  | CS_Rec1 : forall (sb1 : sb) (st1 : st),
      cstep (RECEIVE, state sb1 nil st1) 
            (SKIP ;; RECEIVE, state sb1 nil st1)
  | CS_Rec2 : forall (sb1 : sb) (rb1 : rb) 
                     (st1 : st) (a : aexp) (z : id),
      cstep (RECEIVE, state sb1 (app (cons (a, z) nil) rb1) st1) 
            (z ::= a, state sb1 rb1 st1).

Inductive imp : Type :=
  | machine : id -> com -> State -> imp.

Inductive dist_imp : (imp * imp) -> (imp * imp) -> Prop :=
  | imp_step_1 : forall (c1 c1' c2 : com) (st1 st1' st2 : State) (x y : id),
    cstep (c1, st1) (c1', st1') ->
    dist_imp ((machine x c1 st1), (machine y c2 st2))
               ((machine x c1' st1'), (machine y c2 st2))
  | imp_step_2 : forall (c1 c2' c2 : com) (st1 st2' st2 : State) (x y : id),
    cstep (c2, st2) (c2', st2') ->
    dist_imp ((machine x c1 st1), (machine y c2 st2))
               ((machine x c1 st1), (machine y c2' st2'))
  | send_y : forall (c1 c2 : com) (sb1 sb2 : sb) (rb1 rb2 : rb) (st1 st2 : st)
                    (a : aexp) (x y z : id),
    dist_imp ((machine x c1 (state (cons (a, y, z) sb1) rb1 st1)),
             (machine y c2 (state sb2 rb2 st2)))
            ((machine x c1 (state sb1 rb1 st1)),
            ((machine y c2 (state sb2 (app (cons (a, z) nil) rb2) st2))))
  | send_x : forall (c1 c2 : com) (sb1 sb2 : sb) (rb1 rb2 : rb) (st1 st2 : st)
                    (a : aexp) (x y z : id),
    dist_imp ((machine x c1 (state sb1 rb1 st1)),
             (machine y c2 (state (cons (a, x, z) sb2) rb2 st2))) 
            ((machine x c1 (state sb1 (app (cons (a, z) nil) rb1) st1)),
            (machine y c2 (state sb2 rb2 st2))).

Definition cdist_imp := multi dist_imp.

Lemma proof_of_concept : forall x y n z,
  multi dist_imp ((machine x (SEND (ANum n) TO y CALLED z) empty_state),
                 (machine y (RECEIVE) empty_state))
                 ((machine x SKIP empty_state), 
                 (machine y (z ::= (ANum n)) empty_state)).
Proof. 
  intros. eapply multi_step. apply imp_step_1. 
    eapply CS_Send2. reflexivity.
  eapply multi_step. apply send_y. fold empty_state. 
  eapply multi_step. apply imp_step_2. apply CS_Rec2. fold empty_state. 
  eapply multi_refl.   
Qed.

Lemma proof_of_concept' : forall x y z,
  multi dist_imp ((machine x ((SEND (APlus (APlus (ANum 1) (ANum 1)) (ANum 1))
                      TO y CALLED z) ;; RECEIVE) empty_state),
                  (machine y (RECEIVE ;;
                    SEND (APlus (APlus (ANum 1) (ANum 1)) (ANum 1)) TO x CALLED z)
                    empty_state))
                 ((machine x SKIP (state nil nil (t_update (t_empty 0) z 3))), 
                  (machine y SKIP (state nil nil (t_update (t_empty 0) z 3)))).
Proof.
  intros. 
  eapply multi_step. apply imp_step_2. apply CS_SeqStep. apply CS_Rec1. 
  eapply multi_step. apply imp_step_1. apply CS_SeqStep. apply CS_Send1. 
    apply AS_Plus1. apply AS_Plus.
  eapply multi_step. apply imp_step_1. apply CS_SeqStep. apply CS_Send1. 
    apply AS_Plus.
  eapply multi_step. apply imp_step_1. apply CS_SeqStep. eapply CS_Send2. 
    reflexivity.
  eapply multi_step. apply imp_step_2. apply CS_SeqStep. apply CS_SeqSkip.
  eapply multi_step. apply send_y. 
  eapply multi_step. apply imp_step_2. apply CS_SeqStep. apply CS_Rec2.
  eapply multi_step. apply imp_step_2. apply CS_SeqStep. apply CS_Ass.
  eapply multi_step. apply imp_step_2. apply CS_SeqSkip.
  eapply multi_step. apply imp_step_1. apply CS_SeqSkip.
  eapply multi_step. apply imp_step_2. apply CS_Send1. apply AS_Plus1.
    apply AS_Plus.
  eapply multi_step. apply imp_step_2. apply CS_Send1. apply AS_Plus.
  eapply multi_step. apply imp_step_2. eapply CS_Send2. reflexivity.
  eapply multi_step. apply send_x.
  eapply multi_step. apply imp_step_1. apply CS_Rec2.
  eapply multi_step. apply imp_step_1. apply CS_Ass.
  eapply multi_refl.
Qed.

End DistIMP.

