Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Arith_base Coq.Arith.Even Coq.Arith.Div2.
Require Import Psatz.
Require Import Enum.Util.
Require Import Coq.Program.Wf Init.Wf.
Require Coq.Program.Wf.
Include WfExtensionality.


Inductive Unfair_Pairing : nat -> nat -> nat -> Prop :=
| UnfairPair :
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
  inversion P1; inversion P2; auto.
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

Lemma div2_monotone_Sn : 
  forall n, 
    (div2 n <= div2 (S n)).
Proof.
  apply (ind_0_1_SS (fun n => div2 n <= div2 (S n)));
  [ | | intros n IndHyp; simpl in IndHyp];
  simpl; omega.
Qed.
Hint Resolve div2_monotone_Sn.

Lemma lt_div2' : forall n, div2 n < S n.
Proof.
  intros n.
  apply (le_lt_trans (div2 n) (div2 (S n)) (S n));
    [ apply div2_monotone_Sn |  apply lt_div2 ] ;
    omega.
Qed.
Hint Resolve lt_div2'.

Program Fixpoint unfair_split_x (n : nat) {measure n} :=
  match n with
    | 0 => 0
    | S n' =>
      if (even_odd_dec n)
      then unfair_split_x (div2 n) + 1
      else 0
  end.
Next Obligation.
Proof.
  destruct n'; try (apply lt_n_S); auto.
Qed.

Program Fixpoint unfair_split_y (n : nat) {measure n} :=
  match n with
    | 0 => 0
    | S n' => 
      if (even_odd_dec n)
      then unfair_split_y (div2 n) 
      else div2 (n-1)
  end.
Next Obligation.
Proof.
  destruct n'; try (apply lt_n_S); auto.
Qed.

Lemma pow_not_zero : forall n, 2^n=0 -> False.
Proof.
  induction n.
  simpl.
  intuition.
  unfold pow. fold pow.
  intro PROD.
  apply mult_is_O in PROD;auto.
  destruct PROD; intuition.
Qed.

Lemma unfair_split_recombine : 
  forall n,
    n =
    ((2 ^ (unfair_split_x (S n))) * (2 * (unfair_split_y (S n)) + 1)) - 1.
Proof.
  intros n.
  apply (well_founded_ind
           lt_wf
           (fun n => n =
                     2 ^ unfair_split_x (S n) * (2 * unfair_split_y (S n) + 1)- 1)).
  clear n; intros n IND.

  remember (S n) as m.
  unfold_sub unfair_split_x (unfair_split_x m).
  fold unfair_split_x.
  unfold_sub unfair_split_y (unfair_split_y m).
  fold unfair_split_y.
  destruct m.
  intuition.
  rewrite Heqm; clear Heqm; clear m.

  destruct (even_odd_dec (S n)).
  destruct n.
  inversion e.
  inversion H0.
  
  simpl div2.

  replace (2 ^ (unfair_split_x (S (div2 n)) + 1)) with
  (2 * (2 ^ (unfair_split_x (S (div2 n)))));
    [|(replace (unfair_split_x (S (div2 n)) + 1) 
       with (S (unfair_split_x (S (div2 n))));[|omega]);
       simpl pow;
       nliamega].

  replace (2 * 2 ^ unfair_split_x (S (div2 n)) * (2 * unfair_split_y (S (div2 n)) + 1) - 1)
  with    (2 * (2 ^ unfair_split_x (S (div2 n)) * (2 * unfair_split_y (S (div2 n)) + 1)) - 1);[|nliamega].

  remember (2 ^ unfair_split_x (S (div2 n)) * (2 * unfair_split_y (S (div2 n)) + 1)) as m.
  destruct m.

  destruct (mult_is_O (2 ^ unfair_split_x (S (div2 n)))
                      (2 * unfair_split_y (S (div2 n)) + 1)) as [ZERO|ZERO]; auto.
  apply pow_not_zero in ZERO.
  intuition.

  replace (2 * unfair_split_y (S (div2 n)) + 1) with (S (2 * unfair_split_y (S (div2 n))));[|omega].
  intuition.

  replace (2 ^ unfair_split_x (S (div2 n)) * (2 * unfair_split_y (S (div2 n)) + 1)) 
  with ((2 ^ unfair_split_x (S (div2 n)) * (2 * unfair_split_y (S (div2 n)) + 1) - 1) + 1) in Heqm.
  rewrite <- (IND (div2 n)) in Heqm.
  rewrite Heqm; clear Heqm; clear m.
  unfold mult.
  Type even_double.
  replace (div2 n + 1 + (div2 n + 1 + 0) - 1) with ((div2 n + div2 n) + 1);[|nliamega].
  replace (div2 n + div2 n) with (double (div2 n));[|unfold double;nliamega].
  rewrite <- even_double.
  nliamega.
  inversion e as [|A B C]; inversion B; auto.
  auto.
  nliamega.

  simpl pow.
  replace (S n - 1) with n;[|nliamega].
  inversion o.
  replace (2 * div2 n) with (double (div2 n));[|unfold double;nliamega].
  rewrite <- even_double;auto.
  nliamega.
Qed.

Theorem Unfair_Pairing_from_dec:
  forall n,
    { xy | Unfair_Pairing n (fst xy) (snd xy) }.
Proof.
  intros n.
  exists (unfair_split_x (S n), unfair_split_y (S n)).
  rewrite unfair_split_recombine at 1.
  apply UnfairPair.
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
