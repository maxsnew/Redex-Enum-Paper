Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Arith_base.
Require Import Psatz.

Require Import Util.
Inductive Pairing : nat -> nat -> nat -> Prop :=
| P_XBig :
    forall x y,
      y <= x ->
      Pairing (x*x + x + y) x y
| P_XSmall :
    forall x y,
      x < y ->
      Pairing (x + y*y) x y.
Hint Constructors Pairing.

Theorem Pairing_lt :
  forall m n p,
    Pairing p m n -> (m = 0 /\ n <= 1) \/ (m <= 1 /\ n = 0) \/ (p > m /\ p > n).
Proof.
  intros m n p P.
  inversion P; subst; nliamega.
Qed.

Theorem Pairing_from_fun :
  forall l r n1 n2,
    Pairing n1 l r ->
    Pairing n2 l r ->
    n1 = n2.
Proof.
  intros l r n1 n2 P1 P2.
  inversion P1; inversion P2; subst; nliamega.
Qed.

Lemma Pairing_to_incompat:
  forall l1 l2 r1 r2,
    r1 <= l1 ->
    l2 < r2 ->
    l2 + r2 * r2 = l1 * l1 + l1 + r1 ->
    False.
Proof.
  intros; destruct (eq_nat_dec r2 l1); subst; nliamega.
Qed.

Theorem Pairing_to_fun :
  forall n l1 l2 r1 r2,
    Pairing n l1 r1 ->
    Pairing n l2 r2 ->
    (l1 = l2) /\ (r1 = r2).
Proof.
  intros n l1 l2 r1 r2 P1 P2.
  inversion P1; inversion P2; clear P1; clear P2; subst.

  replace l1 with l2 in * by nliamega.
  replace r1 with r2 in * by nliamega.
  auto.

  cut False. contradiction.
  eapply (Pairing_to_incompat _ _ _ _ H H3 H4).

  cut False. contradiction.
  symmetry in H4.
  eapply (Pairing_to_incompat _ _ _ _ H3 H H4).

  replace r1 with r2 in * by nliamega.
  replace l1 with l2 in * by nliamega.
  auto.
Qed.

Theorem Pairing_to_l_fun :
  forall n l1 l2 r1 r2,
    Pairing n l1 r1 ->
    Pairing n l2 r2 ->
    l1 = l2.
Proof.
  intros n l1 l2 r1 r2 P1 P2.
  edestruct (Pairing_to_fun _ _ _ _ _ P1 P2). auto.
Qed.
Theorem Pairing_to_r_fun :
  forall n l1 l2 r1 r2,
    Pairing n l1 r1 ->
    Pairing n l2 r2 ->
    r1 = r2.
Proof.
  intros n l1 l2 r1 r2 P1 P2.
  edestruct (Pairing_to_fun _ _ _ _ _ P1 P2). auto.
Qed.

Theorem Pairing_to_dec:
  forall x y,
    { n | Pairing n x y }.
Proof.
  intros x y.
  destruct (le_lt_dec y x) as [BIG | SMALL]; eauto.
Defined.

Definition Pairing_to x y : nat := proj1_sig (Pairing_to_dec x y).
Corollary Pairing_to_sound :
  forall l r,
    Pairing (Pairing_to l r) l r.
Proof.
  intros l r. unfold Pairing_to.
  remember (Pairing_to_dec l r) as vn.
  destruct vn as [n P]. simpl. auto.
Qed.
Hint Resolve Pairing_to_sound.

(* sqrt lemmas *)
Lemma sqrt_lemma z : (z - (sqrt z * sqrt z)) - sqrt z <= sqrt z.
Proof.
  destruct (sqrt_spec z); nliamega.
Qed.

Lemma sqrt_lemma' z :
  (z - (sqrt z) * (sqrt z) < (sqrt z))
  -> z = z - (sqrt z * sqrt z) + (sqrt z * sqrt z).
Proof.
  remember (sqrt_spec z); nliamega.
Qed.

Lemma sqrt_lemma'' k n :
  (n * n <= k < S n * S n) -> k - sqrt k * sqrt k - sqrt k < S n.
Proof.
  intros H; rewrite (Nat.sqrt_unique k n); lia.
Qed.

Lemma sqrt_slower_than_id n :
  4 <= n ->
  (S (sqrt (S n))) < n.
Proof.
  intros H4n.
  remember (n - 4) as k.
  replace n with (4 + k) by nliamega.
  clear dependent n.
  rename k into n.
  induction n.
  compute; reflexivity.
  assert (sqrt (S (4 + S n)) <= (S (S (S n)))); [| nliamega].
  eapply le_trans; [apply Nat.sqrt_succ_le|].
  replace (4 + S n) with (S (4 + n)) by nliamega.
  nliamega.
Qed.

Lemma sqrt_4th_root_spread n :
  16 <= n ->
  exists m p,
    m * m <= n < (p * p) * (p * p) /\ p < m.
Proof.
  intros H.
  exists (S (S (sqrt (S (sqrt n))))).
  exists (S (sqrt (S (sqrt n)))).
  split; [| nliamega].
  split; [| destruct (sqrt_spec n); destruct (sqrt_spec (S (sqrt n))); nliamega ].
  destruct (sqrt_spec n).
  apply le_trans with (m := sqrt n * sqrt n); auto.
  assert (S (S (sqrt (S (sqrt n)))) <= sqrt n) as Hperf; [|(apply mult_le_compat; apply Hperf)].
  assert (4 <= sqrt n).
  replace 4 with (sqrt 16) .
  apply Nat.sqrt_le_mono; auto.
  compute; trivial.
  apply sqrt_slower_than_id; auto.
Qed.

Lemma nat_le_iff : forall m p, (forall q : nat, q <= m -> q <= p) <-> m <= p.
Proof.
  split.
  intros H. apply (H m); auto.
  intros H q; nliamega.
Qed.

Lemma nat_lt_iff : forall m p, (forall q : nat, q < m -> q < p) <-> m <= p.
Proof.
  destruct m.
  intros p; split; [nliamega| intros _ q contra; inversion contra].
  destruct p.
  split.
  intros contra; assert (m < 0) by (apply contra; auto); nliamega.
  intros contra; inversion contra.
  split.
  intros H.
  assert (m <= p); [| nliamega].
  apply nat_le_iff.
  intros q Hqm.
  assert (q < S p); [| nliamega].
  apply H; nliamega.
  intros; nliamega.
Qed.

Theorem Pairing_from_dec:
  forall n,
    { xy | Pairing n (fst xy) (snd xy) }.
Proof.
  (* (z - rootz^2, rootz)          if z - rootz^2 <  rootz
     (rootz, (z - rootz^2) -rootz) if z - rootz^2 >= rootz
   *)
  intros z.
  remember (sqrt z) as rootz.
  destruct (le_lt_dec rootz (z - (rootz * rootz))).
  (* P_XBig, x >= y: x*x + x + y *)
  exists (rootz, (z - rootz * rootz) - rootz).
  assert (z = rootz * rootz + rootz + ((z - rootz * rootz) - rootz)) by nliamega.
  assert (((z - (rootz * rootz)) - rootz) = z - (rootz * rootz + rootz)) by nliamega.

  rewrite H at 1.
  constructor 1.
  simpl.

  remember (sqrt_spec z).
  rewrite Heqrootz in *.
  apply sqrt_lemma.

  (* P_XSmall: x < y: x + y*y *)
  exists (z - (rootz * rootz), rootz).
  subst.
  rewrite sqrt_lemma' at 1; [| auto].
  simpl; constructor 2; auto.
Defined.

Definition Pairing_from n : (nat * nat) := proj1_sig (Pairing_from_dec n).
Corollary Pairing_from_sound :
  forall n l r,
    (l, r) = Pairing_from n ->
    Pairing n l r.
Proof.
  intros n l r. unfold Pairing_from.
  remember (Pairing_from_dec n) as vlr.
  destruct vlr as [[l' r'] P]. simpl in *.
  intros EQ. congruence.
Qed.
Hint Resolve Pairing_from_sound.

Theorem Pairing_bound l r k n
: k < S n * S n 
  -> Pairing k l r
  -> l < S n /\ r < S n.
Proof.
  intros H Hp; inversion Hp; subst; nliamega.
Qed.

Ltac rewrite_pairing_to_fun :=
  match goal with
    | [ H1 : Pairing ?x ?y1 ?z1, H2 : Pairing ?x ?y2 ?z2 |- _ ] =>
      destruct (Pairing_to_fun _ _ _ _ _ H1 H2) as [Hl Hr]; rewrite Hl in *; rewrite Hr in *; clear H1 H2 Hl Hr
  end.

Ltac rewrite_pairing_from_fun :=
  match goal with
    | [ H1: Pairing ?n1 ?l ?r, H2: Pairing ?n2 ?l ?r |- _ ] =>
      erewrite (Pairing_from_fun _ _ _ _ H1 H2) in *; clear H1 H2
  end.
