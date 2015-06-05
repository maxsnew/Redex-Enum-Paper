Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Arith_base.
Require Import Psatz.

Require Import Enum.Util.
Inductive Unfair_Pairing : nat -> nat -> nat -> Prop :=
| P :
    forall x y,
      Unfair_Pairing ((pow 2 x) * (2 * y + 1) - 1) x y.
Hint Constructors Unfair_Pairing.

Theorem Unfair_Pairing_from_fun :
  forall l r n1 n2,
    Unfair_Pairing n1 l r ->
    Unfair_Pairing n2 l r ->
    n1 = n2.
Proof.
  intros l r n1 n2 P1 P2.
  inversion P1; inversion P2; subst; nliamega.
Qed.

Theorem Unfair_Pairing_to_fun :
  forall n l1 l2 r1 r2,
    Unfair_Pairing n l1 r1 ->
    Unfair_Pairing n l2 r2 ->
    (l1 = l2) /\ (r1 = r2).
Proof.
  intros n l1 l2 r1 r2 P1 P2.
  inversion P1; inversion P2; clear P1; clear P2; subst.
  admit.
Qed.

Theorem Unfair_Pairing_to_l_fun :
  forall n l1 l2 r1 r2,
    Unfair_Pairing n l1 r1 ->
    Unfair_Pairing n l2 r2 ->
    l1 = l2.
Proof.
  intros n l1 l2 r1 r2 P1 P2.
  edestruct (Unfair_Pairing_to_fun _ _ _ _ _ P1 P2). auto.
Qed.
Theorem Unfair_Pairing_to_r_fun :
  forall n l1 l2 r1 r2,
    Unfair_Pairing n l1 r1 ->
    Unfair_Pairing n l2 r2 ->
    r1 = r2.
Proof.
  intros n l1 l2 r1 r2 P1 P2.
  edestruct (Unfair_Pairing_to_fun _ _ _ _ _ P1 P2). auto.
Qed.

Theorem Unfair_Pairing_to_dec:
  forall x y,
    { n | Unfair_Pairing n x y }.
Proof.
  eauto.
Defined.

Definition Unfair_Pairing_to x y : nat := proj1_sig (Unfair_Pairing_to_dec x y).
Corollary Unfair_Pairing_to_sound :
  forall l r,
    Unfair_Pairing (Unfair_Pairing_to l r) l r.
Proof.
  intros l r. unfold Unfair_Pairing_to.
  remember (Unfair_Pairing_to_dec l r) as vn.
  destruct vn as [n P]. simpl. auto.
Qed.
Hint Resolve Unfair_Pairing_to_sound.

Theorem Unfair_Pairing_from_dec:
  forall n,
    { xy | Unfair_Pairing n (fst xy) (snd xy) }.
Proof.
admit.
Qed.

Definition Unfair_Pairing_from n : (nat * nat) := proj1_sig (Unfair_Pairing_from_dec n).
Corollary Pairing_from_sound :
  forall n l r,
    (l, r) = Unfair_Pairing_from n ->
    Unfair_Pairing n l r.
Proof.
  intros n l r. unfold Unfair_Pairing_from.
  remember (Unfair_Pairing_from_dec n) as vlr.
  destruct vlr as [[l' r'] P]. simpl in *.
  intros EQ. congruence.
Qed.
Hint Resolve Pairing_from_sound.

Ltac rewrite_unfair_pairing_to_fun :=
  match goal with
    | [ H1 : Unfair_Pairing ?x ?y1 ?z1, H2 : Unfair_Pairing ?x ?y2 ?z2 |- _ ] =>
      destruct (Unfair_Pairing_to_fun _ _ _ _ _ H1 H2) as [Hl Hr]; rewrite Hl in *; rewrite Hr in *; clear H1 H2 Hl Hr
  end.

Ltac rewrite_unfair_pairing_from_fun :=
  match goal with
    | [ H1: Unfair_Pairing ?n1 ?l ?r, H2: Unfair_Pairing ?n2 ?l ?r |- _ ] =>
      erewrite (Unfair_Pairing_from_fun _ _ _ _ H1 H2) in *; clear H1 H2
  end.

(* Local Variables: *)
(* coq-load-path: (("." "Enum")) *)
(* end: *)
