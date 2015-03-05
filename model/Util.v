Require Import Coq.Logic.Eqdep_dec.
Require Import Omega.
Require Import Psatz.

Ltac nliamega := try omega; try lia; try nia; fail "omega, lia and nia all failed".

(* Turn hypotheses of shape (existT h1 h2 l = existT h1 h2 r) into l = r if equality on lhs is decidable *)
Ltac dec_K :=
  match goal with
    | [ H : existT ?P ?L ?x = existT ?P ?L ?y |- _ ] => apply inj_pair2_eq_dec in H;
        [subst |]; auto
  end.

(* Try possible contradictions *)
Ltac mycontra :=
  match goal with
    | [ H: context[_ -> False] |- False ] =>
      eapply H; eauto; fail
  end.

(* sumbool notation a la cpdt *)
Notation Yes := (left _).
Notation No := (right _).
Notation "l &&& r" := (if l then r else No) (at level 70).
Notation Refine x := (if x then Yes else No).

(* sumor notation a la cpdt *)
Notation "{{ x }}" := (exist _ x _).

Ltac sumbool_contra :=
  match goal with
    | [ H: inl _ = inr _ |- _ ] => inversion H
    | [ H: inr _ = inl _ |- _ ] => inversion H
  end.

Ltac destruct_eq :=
  match goal with
    | [ H: (?x1, ?y1) = (?x2, ?y2) |- _ ] =>
      (assert (x1 = x2) by congruence); (assert (y1 = y2) by congruence); subst; clear H
    | [ H: inl ?x = inl ?y |- _ ] => (assert (x = y) by congruence); subst; clear H
    | [ H: inr ?x = inr ?y |- _ ] => (assert (x = y) by congruence); subst; clear H
  end.

Ltac split4 := split; [| split; [| split]].
Ltac destruct4 H := destruct H as [? [? [? ?]]].
