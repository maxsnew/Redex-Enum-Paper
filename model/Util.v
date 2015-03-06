Require Import Coq.Logic.Eqdep.
Require Import Omega.
Require Import Psatz.

Ltac nliamega := try omega; try lia; try nia; fail "omega, lia and nia all failed".

(* Turn hypotheses of shape (existT h1 h2 l = existT h1 h2 r) into l = r if equality on lhs is decidable *)

Ltac inj_crush :=
  repeat (
      match goal with
        | [ x : prod ?t1 ?t2 |- _] => destruct x
        | [ x : sum ?t1 ?t2 |- _] => destruct x
      end).

Ltac my_crush :=
  repeat (
      match goal with
        | [ |- forall x, _ ] => intros
        | [|- _ /\ _ ] => split
        | [H: _ /\ _ |- _ ] => destruct H
        | [ |- context[if ?x then _ else _] ] => destruct x
        | _ => auto
      end
    ).

(* Try possible contradictions *)
Ltac mycontra :=
  match goal with
    | [ H: context[_ -> False] |- False ] =>
      eapply H; eauto; fail
  end.

(* sumbool notation a la cpdt *)
Notation Yes := (left _).
Notation No := (right _).
Notation Refine x := (if x then Yes else No).
Notation "l &&& r" := (if l then Refine r else No) (at level 70).

(* sumor notation a la cpdt *)
Notation "{{ x }}" := (exist _ x _).

Ltac sumbool_contra :=
  match goal with
    | [ H: inl _ = inr _ |- _ ] => inversion H
    | [ H: inr _ = inl _ |- _ ] => inversion H
  end.

Ltac destruct_eq :=
  match goal with
    | [ H : existT ?P ?L ?x = existT ?P ?L ?y |- _ ] => apply inj_pair2 in H; subst
    | [ H: (?x1, ?y1) = (?x2, ?y2) |- _ ] =>
      (assert (x1 = x2) by congruence); (assert (y1 = y2) by congruence); subst; clear H
    | [ H: inl ?x = inl ?y |- _ ] => (assert (x = y) by congruence); subst; clear H
    | [ H: inr ?x = inr ?y |- _ ] => (assert (x = y) by congruence); subst; clear H
  end.

Ltac split4 := split; [| split; [| split]].
Ltac destruct4 H := destruct H as [? [? [? ?]]].
