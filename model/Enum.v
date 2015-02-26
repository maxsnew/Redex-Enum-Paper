Require Import Omega.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Div2 Coq.Arith.Even.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Psatz.

Ltac nliamega := try omega; try lia; try nia; fail "omega, lia and nia all failed".

Inductive Value : Set :=
| V_Nat : nat -> Value
| V_Pair : Value -> Value -> Value
| V_Sum_Left : Value -> Value
| V_Sum_Right : Value -> Value.
Hint Constructors Value.

Definition Bijection (A:Set) (B:Set) :=
  { fg : (A->B)*(B->A) |
    (forall (a:A),
      (snd fg) ((fst fg) a) = a)
    /\
    (forall (b:B),
      (fst fg) ((snd fg) b) = b) }.
Definition biject_to {A} {B} (bi:Bijection A B) (a:A) : B :=
  (fst (proj1_sig bi)) a.
Definition biject_from {A} {B} (bi:Bijection A B) (b:B) : A :=
  (snd (proj1_sig bi)) b.

Definition Bijects {A:Set} {B:Set} (bi:Bijection A B) (a:A) (b:B) :=
  biject_to bi a = b
  /\ biject_from bi b = a.

Lemma Bijects_fun_right:
  forall A B (b:Bijection A B) x y1 y2,
    Bijects b x y1 ->
    Bijects b x y2 ->
    y1 = y2.
Proof.
  intros A B b x y1 y2.
  intros [B1_l B1_r] [B2_l B2_r].
  congruence.
Qed.
Lemma Bijects_fun_left:
  forall A B (b:Bijection A B) x1 x2 y,
    Bijects b x1 y ->
    Bijects b x2 y ->
    x1 = x2.
Proof.
  intros A B b x1 x2 y.
  intros [B1_l B1_r] [B2_l B2_r].
  congruence.
Qed.

Definition Bijects_to_dec :
  forall A B (bi:Bijection A B) a,
    { b | Bijects bi a b }.
Proof.
  intros. exists (biject_to bi a).
  unfold Bijects. intuition.
  unfold biject_from, biject_to.
  destruct bi as [[f g] [F G]].
  simpl in *. auto.
Defined.

Definition Bijects_from_dec :
  forall A B (bi:Bijection A B) b,
    { a | Bijects bi a b }.
Proof.
  intros. exists (biject_from bi b).
  unfold Bijects. intuition.
  unfold biject_from, biject_to.
  destruct bi as [[f g] [F G]].
  simpl in *. auto.
Defined.

Inductive tag : Set :=
| zero  : tag
| one   : tag
| two   : tag
| three : tag.

Inductive Enum : Set :=
| E_Nat : Enum
| E_Pair : Enum -> Enum -> Enum
| E_Map : Bijection Value Value -> Enum -> Enum
| E_Dep : Enum -> (Value -> Enum) -> Enum
| E_Sum : Enum -> Enum -> Enum
| E_Trace : tag -> Enum -> Enum (* A no-op wrapper to signal tracing *)
.

Hint Constructors Enum.

Section Pairing.
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

  Section Sqrt.
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


  End Sqrt.

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

  Theorem Pairing_bound l r k n
  : k < S n * S n 
    -> Pairing k l r
    -> l < S n /\ r < S n.
  Proof.
    intros H Hp; inversion Hp; subst; nliamega.
  Qed.

End Pairing.
(* TODO: find out how to make hints go out of their section *)
Hint Constructors Pairing.
Hint Resolve Pairing_to_sound.
Hint Resolve Pairing_from_sound.

Notation set' := (set nat).
Notation empty_set' := (@empty_set nat).
Notation set_union' := (@set_union nat eq_nat_dec).
Notation set_add' := (@set_add nat eq_nat_dec).
Section Sets.
  Fixpoint subset (s1 s2 : set nat) :=
    match s1 with
      | nil => True
      | x :: more =>
        set_In x s2 /\ subset more s2
    end.
  Hint Unfold subset.

  Theorem subset_nil : forall s, subset nil s.
  Proof.
    auto.
  Qed.

  Theorem subset_nil_nil : forall s, subset s nil -> s = nil.
  Proof.
    induction s.
    auto.
    intros contra.
    unfold subset in contra.
    destruct contra.
    inversion H.
  Qed.

  Definition set_eq s1 s2 := subset s1 s2 /\ subset s2 s1.
  Hint Unfold set_eq.

  Lemma subset_consr s1 s2 n : subset s1 s2 -> subset s1 (cons n s2).
  Proof.
    generalize dependent s2.
    generalize dependent n.
    induction s1.
    constructor.

    intros n s2 H.
    unfold subset.
    unfold subset in H.
    destruct H.
    fold subset in *.

    split.
    constructor 2; auto.
    apply IHs1; auto.
  Defined.

  Definition subset_dec s1 s2 : { subset s1 s2 } + { ~ (subset s1 s2) }.
  Proof.
    generalize dependent s2.
    induction s1.
    left; auto.

    intros s2.
    destruct (In_dec eq_nat_dec a s2).

    destruct (IHs1 s2).
    left; constructor; auto.

    right.
    unfold subset; fold subset.
    intros H; destruct H; contradiction.

    right.
    intros H; destruct H; contradiction.
  Defined.

  Definition subset_nn s1 s2 : ~~(subset s1 s2) -> subset s1 s2.
  Proof.
    destruct (subset_dec s1 s2); tauto.
  Qed.

  Definition set_eq_dec s1 s2 : { set_eq s1 s2 } + { ~ (set_eq s1 s2) }.
  Proof.
    destruct (subset_dec s1 s2).
    destruct (subset_dec s2 s1).
    left; auto.
    right; intros contra; destruct contra; apply n; auto.
    right; intros contra; destruct contra; apply n; auto.
  Qed.

  Theorem subset_refl s : subset s s.
  Proof.
    induction s; unfold subset; auto.
    fold subset.
    split.
    constructor 1; auto.
    apply subset_consr; auto.
  Qed.

  Theorem set_eq_refl s : set_eq s s.
  Proof.
    split; apply subset_refl.
  Qed.

  Theorem subset_In : forall x s s', set_In x s -> subset s s' -> set_In x s'.
  Proof.
    intros x s.
    generalize dependent x.
    induction s as [| x s].
    intros y s contra.
    inversion contra.

    intros y s' Hyinxs Hsub.
    destruct Hsub as [Hxins' Hsub].
    destruct Hyinxs; subst; auto.
  Qed.

  Theorem subset_In_def s s' : (forall x, set_In x s -> set_In x s') -> subset s s'.
  Proof.
    generalize dependent s'.
    induction s.
    intros; apply subset_nil.
    split.
    apply H; auto.
    constructor; auto.
    apply IHs.
    intros x Hins.
    apply H.
    constructor 2; auto.
  Qed.

  Theorem In_subset_def s s' : subset s s' -> (forall x, set_In x s -> set_In x s').
  Proof.
    generalize dependent s'.
    induction s.
    intros s' _ x contra.
    inversion contra.

    intros s' Hsub x Hin.
    destruct Hin.
    destruct Hsub; subst.
    auto.

    apply IHs.
    destruct Hsub; subst; auto.
    auto.
  Qed.

  Hint Resolve subset_In_def In_subset_def.
  Theorem subset_In_equiv s s' : subset s s' <-> (forall x, set_In x s -> set_In x s').
  Proof.
    split; eauto.
  Qed.

  Lemma set_subset_weaken : forall s1 s2, set_eq s1 s2 -> subset s1 s2.
  Proof.
    unfold set_eq.
    tauto.
  Qed.

  Theorem not_subset_In_def s s' x : set_In x s -> ~(set_In x s') -> ~ subset s s'.
  Proof.
    intros; eauto.
  Qed.

  Lemma subset_trans : forall s1 s2 s3, subset s1 s2 -> subset s2 s3 -> subset s1 s3.
  Proof.
    intros s1.
    induction s1 as [| x s1].
    intros; apply subset_nil.
    induction s2 as [| y s2].
    intros s3 contra.
    inversion contra.
    inversion H.

    intros s3 Hxy12 Hy23.
    unfold subset; fold subset.
    destruct Hxy12 as [Hxy2 H1y2].
    split.

    eapply subset_In.
    apply Hxy2.
    auto.
    apply IHs1 with (s2 := (y :: s2)); auto.
  Qed.


  Lemma set_eq_trans : forall s1 s2 s3, set_eq s1 s2 -> set_eq s2 s3 -> set_eq s1 s3.
  Proof.
    unfold set_eq.
    intros s1 s2 s3 H1 H2; destruct H1; destruct H2.
    split; eapply subset_trans; eauto.
  Qed.

  Lemma set_eq_symm : forall s1 s2, set_eq s1 s2 -> set_eq s2 s1.
  Proof.
    intros s1 s2 H; inversion H; split; auto.
  Qed.

  (* Theorem set_union_or : forall s1 s2, subset s1 (set_union' s1 s2). *)

  Lemma set_add_subset : forall x s1 s2, set_In x s2 -> subset s1 s2 -> subset (set_add' x s1) s2.
  Proof.

    intros y s1.
    induction s1 as [| x s1].
    simpl; auto.
    intros s2 Hy2 Hsub.
    unfold set_add.
    destruct (eq_nat_dec y x); subst; auto.
    fold set_add.
    unfold subset.
    split; auto.
    destruct Hsub; auto.
    fold subset.
    apply IHs1; auto.
    destruct Hsub; auto.
  Qed.

  Lemma subset_cons_swap : forall x y s1 s2, subset s1 s2 -> subset (x :: y :: s1) (y :: x :: s2).
  Proof.
    intros x y s1 s2.
    destruct (eq_nat_dec x y).
    simpl; subst.
    split.
    tauto.
    split.
    tauto.
    apply subset_consr.
    apply subset_consr.
    assumption.

    simpl.
    split.
    tauto.
    split.
    tauto.
    apply subset_consr. apply subset_consr.
    assumption.
  Qed.

  Lemma set_eq_cons_swap : forall x y s1 s2, set_eq s1 s2 -> set_eq (x :: y :: s1) (y :: x :: s2).
  Proof.
    split; destruct H; apply subset_cons_swap; auto.
  Qed.

  Lemma set_cons_cons_subset : forall x s1 s2, subset s1 s2 -> subset (x :: s1) (x :: s2).
  Proof.
    intros x s1 s2 Hsub.
    unfold subset. fold subset.
    split.
    constructor; auto.
    apply subset_consr; auto.
  Qed.

  Lemma set_eq_cons_cons x s1 s2 : set_eq s1 s2 -> set_eq (x :: s1) (x :: s2).
  Proof.
    intros H.
    destruct H.
    split; apply set_cons_cons_subset; auto.
  Qed.

  Lemma set_add_cons_eq : forall x s, set_eq (x :: s) (set_add' x s).
  Proof.
    split.
    generalize dependent x.
    induction s as [| y s].
    compute; tauto.
    intros x.
    simpl.
    destruct (eq_nat_dec x y); subst.
    split.
    constructor; auto.
    split.
    constructor; auto.
    apply subset_consr.
    apply subset_refl.

    split.
    destruct (IHs x).
    apply in_cons. apply H.
    split.
    constructor; auto.
    apply subset_trans with (s2:= (x :: s)).
    apply subset_consr; auto.

    apply subset_trans with (s2 := (set_add' x s)).
    apply IHs.
    apply subset_consr.
    apply subset_refl.

    generalize dependent x.
    induction s as [| y s].
    compute; tauto.
    intros x.
    simpl.
    destruct (eq_nat_dec x y).
    apply subset_consr.
    apply subset_refl.
    apply subset_trans with (y :: x :: s).
    apply set_cons_cons_subset.
    apply IHs.
    apply subset_cons_swap.
    apply subset_refl.
  Qed.

  Lemma set_add_cons_subset : forall x s1 s2, subset s1 s2 -> subset (x :: s1) (set_add' x s2).
  Proof.
    intros x s1 s2 Hsub.
    apply subset_trans with (s2 := (x :: s2)).
    apply set_cons_cons_subset; auto.
    apply set_subset_weaken.
    apply set_add_cons_eq.
  Qed.

  Lemma set_union_unitl : forall s, set_eq (set_union' empty_set' s) s.
  Proof.
    split.
    induction s.
    apply subset_refl.

    unfold set_union in *.
    replace (((fix set_union (x y : set nat) {struct y} :
                 set nat :=
                 match y with
                   | nil => x
                   | a1 :: y1 => set_add eq_nat_dec a1 (set_union x y1)
                 end) empty_set' s
            )) with (set_union' empty_set' s) in * by auto.
    fold set_add'.
    apply set_add_subset; auto.
    constructor; auto.
    apply subset_consr; auto.

    induction s; auto.
    unfold set_union.
    fold set_union.
    apply set_add_cons_subset; auto.
  Qed.

  Lemma set_union_unitr : forall s, set_eq (set_union' s empty_set') s.
  Proof.
    apply set_eq_refl.
  Qed.

  Lemma elem_union :
    forall s x,
      set_In x s -> forall s', set_In x (set_union' s' s).
  Proof.
    induction s.
    intros H contra.
    inversion contra.

    intros x Hin s'.
    simpl.
    assert (set_In x (a :: (set_union' s' s))).
    destruct Hin.
    constructor; auto.
    eapply In_subset_def.
    apply subset_consr.
    apply subset_refl.
    apply IHs; auto.
    eapply In_subset_def.
    apply set_add_cons_subset.
    apply subset_refl.
    auto.
  Qed.

  Lemma subset_union_cons : forall x s1 s2, subset (set_union' (x::s1) s2) (x :: (set_union' s1 s2)).
    induction s2.
    simpl; split.
    tauto.
    apply subset_consr; apply subset_refl.
    simpl.
    eapply subset_trans.
    apply set_add_cons_eq.
    apply subset_trans with (s2 := (x :: a :: (set_union' s1 s2))).
    eapply subset_trans.
    apply set_cons_cons_subset.
    apply IHs2.
    apply subset_cons_swap.
    apply subset_refl.
    apply set_cons_cons_subset.
    apply set_add_cons_eq.
  Qed.

  Theorem subset_union_comm : forall s1 s2, subset (set_union' s1 s2) (set_union' s2 s1).
  Proof.
    induction s1.
    intros.
    apply subset_trans with (s2 := s2).
    apply set_union_unitl.
    apply set_union_unitr.

    intros s2.
    simpl.
    eapply subset_trans.
    apply subset_union_cons.
    apply set_add_cons_subset.
    apply IHs1.
  Qed.

  Theorem set_eq_union_comm : forall s1 s2, set_eq (set_union' s1 s2) (set_union' s2 s1).
  Proof.
    intros s1 s2.
    split; apply subset_union_comm.
  Qed.

  Lemma subset_union_transr :
    forall s sl sr,
      subset s sr ->
      subset s (set_union' sl sr).
  Proof.
    intros.
    apply subset_In_def.
    intros x Hin.
    apply elem_union.
    eapply In_subset_def.
    apply H.
    auto.
  Qed.

  Lemma subset_union_transl :
    forall s sl sr,
      subset s sl ->
      subset s (set_union' sl sr).
  Proof.
    intros.
    eapply subset_trans; [| apply subset_union_comm ].
    apply subset_union_transr; auto.
  Qed.


  Lemma set_union_subset_cong :
    forall sl sr sl' sr',
      subset sl sl' -> subset sr sr' -> subset (set_union' sl sr) (set_union' sl' sr').
  Proof.
    induction sr.
    intros.
    apply subset_trans with (s2 := sl).
    apply set_union_unitr.
    apply subset_union_transl; auto.

    intros sl' sr' Hsubl Hsubr.
    simpl.
    apply subset_trans with (s2 := (a :: set_union' sl sr)).
    apply set_subset_weaken.
    apply set_eq_symm.
    apply set_add_cons_eq.
    simpl.
    split.
    apply elem_union.
    destruct Hsubr; auto.
    apply IHsr; auto.
    eapply subset_trans.
    eapply subset_consr.
    apply subset_refl.
    apply Hsubr.
  Qed.

  Lemma set_union_cong : forall sl sr sl' sr',
                           set_eq sl sl' -> set_eq sr sr' -> set_eq (set_union' sl sr) (set_union' sl' sr').
  Proof.
    intros sl sr sl' sr' Hl Hr.
    destruct Hl as [Hl Hl'].
    destruct Hr as [Hr Hr'].
    split; apply set_union_subset_cong; auto.
  Qed.


  Lemma set_subset_add : forall x s1 s2, subset s1 s2 -> subset s1 (set_add' x s2).
  Proof.
    intros x s1 s2 Hsub.
    eapply subset_trans; [| apply set_add_cons_subset; apply subset_refl ].
    apply subset_consr; auto.
  Qed.

  Theorem set_eq_app_cons_comm s1 s2 a : set_eq (a :: (s1 ++ s2)) (s1 ++ a :: s2).
  Proof.
    induction s1.
    apply set_eq_refl.
    rewrite <-app_comm_cons.
    eapply set_eq_trans.
    apply set_eq_cons_swap.
    apply set_eq_refl.
    replace ((a0 :: s1) ++ a :: s2) with (a0 :: (s1 ++ a :: s2)) by apply app_comm_cons.
    apply set_eq_cons_cons; auto.
  Qed.

  Theorem set_union_app_eq : forall s1 s2, set_eq (set_union' s1 s2) (s1 ++ s2).
  Proof.
    induction s2.
    simpl.
    rewrite app_nil_r.
    apply set_eq_refl.

    simpl.
    eapply set_eq_trans.
    apply set_eq_symm.
    apply set_add_cons_eq.
    eapply set_eq_trans; [|   apply set_eq_app_cons_comm].
    apply set_eq_cons_cons; auto.
  Qed.

  Theorem set_union_app_eq_gen : forall s1 s2 s3 s4,
                                   set_eq s1 s3 ->
                                   set_eq s2 s4 ->
                                   set_eq (set_union' s1 s2) (s3 ++ s4).
  Proof.
    intros s1 s2 s3 s4 H13 H24.
    eapply set_eq_trans; [| apply set_union_app_eq].
    apply set_union_cong; auto.
  Qed.


  Theorem subset_union_both s sl sr
  : subset sl s -> subset sr s -> subset (set_union' sl sr) s.
  Proof.
    intros Hls Hrs.
    apply subset_In_def.
    intros x Hin.
    destruct (set_union_elim eq_nat_dec x sl sr).
    apply Hin.
    apply In_subset_def with sl; auto.
    apply In_subset_def with sr; auto.
  Qed.

  Theorem subset_union_eq : forall s1 s2, subset s1 s2 -> set_eq (set_union' s1 s2) s2.
  Proof.
    split; [| apply subset_union_transr; apply subset_refl ].
    generalize dependent s2.
    induction s1 as [| x s1].
    intros s1 Hsubnil.
    apply subset_trans with (s2 := s1).
    apply set_union_unitl; apply subset_refl.
    apply subset_refl.

    intros s2 Hsub.
    apply subset_trans with (s2 := x :: (set_union' s1 s2)).
    apply subset_trans with (s2 := (x :: s1 ++ s2)).
    apply set_union_app_eq.
    apply set_subset_weaken.
    apply set_eq_cons_cons.
    apply set_eq_symm.
    apply set_union_app_eq.

    simpl.
    unfold subset in Hsub; fold subset in Hsub.
    destruct Hsub.
    split; auto.
  Qed.

  Theorem set_union_assoc s1 s2 s3
  : set_eq (set_union' (set_union' s1 s2) s3)
           (set_union' s1 (set_union' s2 s3)).
  Proof.
    apply set_eq_trans with (s2 := ((s1 ++ s2) ++ s3)).
    apply set_union_app_eq_gen.
    apply set_union_app_eq.
    apply set_eq_refl.
    rewrite <-app_assoc.
    apply set_eq_symm.
    apply set_union_app_eq_gen.
    apply set_eq_refl.
    apply set_union_app_eq.
  Qed.

  Example set_eq_test : (set_eq (set_add' 1 (set_add' 0 empty_set'))
                                (set_add' 0 (set_add' 1 empty_set'))).
  Proof.
    compute.
    tauto.
  Qed.

  Lemma subset_app : forall s1 s2 s3, subset s1 s2 -> subset s1 (s2 ++ s3).
  Proof.
    induction s1; auto.
    induction s2.

    intros s3 H.
    inversion H.
    inversion H0.

    intros s3.
    simpl.
    rewrite app_comm_cons.
    intros H.
    destruct H.
    destruct H.
    subst.
    split.
    left; auto.
    apply IHs1; auto.

    split.
    right.
    unfold set_In.
    apply in_or_app.
    left; auto.

    apply IHs1; auto.
  Qed.
  Lemma subset_rev : forall s, subset s (rev s).
  Proof.
    induction s; auto.
    constructor.
    rewrite <-in_rev.
    constructor; auto.
    replace (a :: s) with ((a :: nil) ++ s).
    rewrite rev_app_distr.
    apply subset_app; auto.

    auto.
  Qed.

  Lemma set_eq_rev : forall s, set_eq s (rev s).
  Proof.
    split; try apply subset_rev.
    rewrite <-rev_involutive.
    apply subset_rev.
  Qed.
  
  Fixpoint z_to_n n : set nat :=
    match n with
      | 0 => empty_set'
      | S n' => set_add' n' (z_to_n n')
    end.

  Definition n_to_z n : set nat := rev (z_to_n n).

  Theorem z_to_n_correct n x
  : set_In x (z_to_n n) <-> x < n.
  Proof.
    generalize dependent x.
    induction n.

    intros x; compute; split; [apply False_ind | intros contra; inversion contra].
    intros x.
    destruct (eq_nat_dec x n).
    simpl.
    subst.
    split; [nliamega|].
    intros _.
    apply set_add_intro2; auto.

    split.
    simpl.
    intros H.
    assert (set_In x (z_to_n n)).
    apply set_add_elim2 with (b := n) (Aeq_dec := eq_nat_dec); auto.
    assert (x < n).
    apply IHn.
    auto.
    nliamega.

    intros H.
    simpl.
    apply set_add_intro1.
    apply IHn.
    nliamega.
  Qed.

  Lemma z_to_n_nosubS m : ~ subset (z_to_n (S m)) (z_to_n m).
  Proof.
    intros H.
    assert (set_In m (z_to_n m)).
    eapply In_subset_def; eauto.
    apply z_to_n_correct; nliamega.
    rewrite z_to_n_correct in H0.
    nliamega.
  Qed.

  Lemma z_to_n_nosub' m n : ~ subset (z_to_n (S (m + n))) (z_to_n m).
  Proof.
    induction n.
    replace (m + 0) with m by nliamega.
    apply z_to_n_nosubS.
    unfold z_to_n; fold z_to_n.
    replace (m + S n) with (S (m + n)) by nliamega.
    intros H.
    apply IHn.
    apply subset_In_def.
    intros x.
    rewrite z_to_n_correct.
    intros Hlt.
    assert (set_In x (set_add' (S (m + n)) (z_to_n (S (m + n))))).
    replace (set_add' (S (m + n)) (z_to_n (S (m + n)))) with (z_to_n (S (S (m + n)))).
    apply z_to_n_correct; nliamega.
    trivial.
    eapply In_subset_def.
    apply H.
    auto.
  Qed.

  Lemma z_to_n_nosub m n : m < n -> ~ subset (z_to_n n) (z_to_n m).
  Proof.
    intros H1 H2.
    destruct n; [nliamega|].
    assert (n < m); [| nliamega].
    apply z_to_n_correct.
    eapply In_subset_def.
    eapply subset_trans; eauto.
    unfold set_In.
    rewrite !z_to_n_correct; auto.
  Qed.


End Sets.
Hint Resolve set_eq_refl.
Hint Resolve subset_refl.

Ltac split4 := split; [| split; [| split]].
Ltac destruct4 H := destruct H as [? [? [? ?]]].
Section Traces.
  Inductive Trace :=
  | Tracing : set' -> set' -> set' -> set' -> Trace.

  Definition trace_proj tg t :=
    match t with
      | Tracing t0 t1 t2 t3 =>
        match tg with
          | zero  => t0
          | one   => t1
          | two   => t2
          | three => t3
        end
    end.


  Definition trace_zero : Trace := Tracing empty_set' empty_set' empty_set' empty_set'.
  Definition trace_plus (t1 t2 : Trace) : Trace :=
    match (t1, t2) with
      | (Tracing l1 l2 l3 l4, Tracing r1 r2 r3 r4) =>
        Tracing (set_union' l1 r1)
                (set_union' l2 r2)
                (set_union' l3 r3)
                (set_union' l4 r4)
    end.

  Definition trace_one n t : Trace :=
    match t with
      | zero  => Tracing (set_add' n empty_set') empty_set' empty_set' empty_set'
      | one   => Tracing empty_set' (set_add' n empty_set') empty_set' empty_set'
      | two   => Tracing empty_set' empty_set' (set_add' n empty_set') empty_set'
      | three => Tracing empty_set' empty_set' empty_set' (set_add' n empty_set')
    end.

  Definition trace_eq (t1 t2 : Trace) : Prop :=
    match (t1, t2) with
      | (Tracing l0 l1 l2 l3, Tracing r0 r1 r2 r3) =>
        set_eq l0 r0
        /\ set_eq l1 r1
        /\ set_eq l2 r2
        /\ set_eq l3 r3
    end.

  Definition sub_trace (t1 t2 : Trace) : Prop :=
    match (t1, t2) with
      | (Tracing l0 l1 l2 l3, Tracing r0 r1 r2 r3) =>
        subset l0 r0
        /\ subset l1 r1
        /\ subset l2 r2
        /\ subset l3 r3
    end.

  Theorem sub_trace_refl t : sub_trace t t.
  Proof.
    unfold sub_trace; destruct t; split4; apply subset_refl.
  Qed.

  Theorem sub_trace_trans t1 t2 t3 : sub_trace t1 t2 -> sub_trace t2 t3 -> sub_trace t1 t3.
  Proof.
    unfold sub_trace; destruct t1, t2, t3.
    intros H1 H2; destruct4 H1; destruct4 H2.
    split4; eapply subset_trans; eauto.
  Qed.

  Theorem sub_trace_zero t : sub_trace trace_zero t.
  Proof. destruct t; compute; tauto. Qed.

  Theorem trace_eq_proj t1 t2 tg : trace_eq t1 t2 -> set_eq (trace_proj tg t1) (trace_proj tg t2).
  Proof.
    unfold trace_eq, trace_proj; destruct t1; destruct t2; destruct tg; intuition.
  Qed.

  Theorem sub_trace_proj t1 t2 tg : sub_trace t1 t2 -> subset (trace_proj tg t1) (trace_proj tg t2).
  Proof.
    unfold sub_trace; destruct t1; destruct t2; destruct tg; intuition.
  Qed.

  Definition trace_eq' t1 t2 : Prop :=
    sub_trace t1 t2 /\ sub_trace t2 t1.
  Theorem trace_eq'_weakenl t1 t2 : trace_eq' t1 t2 -> sub_trace t1 t2.
  Proof. unfold trace_eq'; intuition. Qed.
  Theorem trace_eq'_weakenr t1 t2 : trace_eq' t1 t2 -> sub_trace t2 t1.
  Proof. unfold trace_eq'; intuition. Qed.
  Theorem trace_eq_eq'_equiv t1 t2 : trace_eq t1 t2 <-> trace_eq' t1 t2.
  Proof.
    unfold trace_eq, trace_eq', sub_trace, set_eq;
    destruct t1; destruct t2; intuition.
  Qed.

  Theorem trace_eq_weakenl t1 t2 : trace_eq t1 t2 -> sub_trace t1 t2.
  Proof. rewrite trace_eq_eq'_equiv; apply trace_eq'_weakenl. Qed.

  Theorem trace_eq_weakenr t1 t2 : trace_eq t1 t2 -> sub_trace t2 t1.
  Proof. rewrite trace_eq_eq'_equiv; apply trace_eq'_weakenr. Qed.

  Theorem trace_plus_cong t1 t2 t3 t4 : trace_eq t1 t3 -> trace_eq t2 t4 -> trace_eq (trace_plus t1 t2) (trace_plus t3 t4).
    unfold trace_eq.
    destruct t1; destruct t2; destruct t3; destruct t4.
    unfold trace_plus.
    intros H; destruct4 H.
    intros H'; destruct4 H'.
    split4; apply set_union_cong; auto.
  Qed.

  Theorem trace_eq_refl t : trace_eq t t.
  Proof.
    unfold trace_eq; destruct t; split4; apply set_eq_refl.
  Qed.


  Theorem trace_eq_symm t1 t2 : trace_eq t1 t2 -> trace_eq t2 t1.
  Proof.
    unfold trace_eq.
    destruct t1; destruct t2.
    intros H; destruct4 H.
    split4; apply set_eq_symm; auto.
  Qed.

  Theorem trace_eq_trans t1 t2 t3 : trace_eq t1 t2 -> trace_eq t2 t3 -> trace_eq t1 t3.
  Proof.
    unfold trace_eq.
    destruct t1; destruct t2; destruct t3.
    intros H; destruct4 H.
    intros H'; destruct4 H'.
    split4; eapply set_eq_trans; eauto.
  Qed.

  Theorem trace_plus_comm t1 t2 : trace_eq (trace_plus t1 t2) (trace_plus t2 t1).
  Proof.
    destruct t1, t2.
    unfold trace_plus.
    split4; apply set_eq_union_comm.
  Qed.

  Theorem trace_plus_assoc t1 t2 t3 : trace_eq (trace_plus t1 (trace_plus t2 t3))
                                               (trace_plus (trace_plus t1 t2) t3).
  Proof.
    destruct t1, t2, t3.
    unfold trace_plus.
    split4; apply set_eq_symm; apply set_union_assoc.
  Qed.

  Theorem sub_trace_plus_transl t tl tr
  : sub_trace t tl -> sub_trace t (trace_plus tl tr).
  Proof.
    intros H; destruct t; destruct tl; destruct tr;
    destruct4 H; split4; apply subset_union_transl; auto.
  Qed.

  Theorem sub_trace_plus_transr t tl tr
  : sub_trace t tr -> sub_trace t (trace_plus tl tr).
  Proof.
    intros H.
    eapply sub_trace_trans.
    Focus 2.
    apply trace_eq_weakenl.
    apply trace_plus_comm.
    apply sub_trace_plus_transl; auto.
  Qed.

  Theorem sub_trace_plus_eq : forall t1 t2, sub_trace t1 t2 -> trace_eq (trace_plus t1 t2) t2.
  Proof.
    intros t1 t2 H; destruct t1; destruct t2;
      destruct4 H; split4; apply subset_union_eq; auto.
  Qed.

  Theorem trace_plus_unitl t :
    trace_eq (trace_plus trace_zero t) t.
  Proof.
    destruct t; split4; apply set_union_unitl.
  Qed.

  Theorem trace_plus_unitl_gen t1 t2 :
    trace_eq t1 t2 -> trace_eq (trace_plus trace_zero t1) t2.
  Proof.
    intros H.
    eapply trace_eq_trans; [ apply trace_plus_unitl | auto].
  Qed.


  Theorem trace_plus_unitr t :
    trace_eq (trace_plus t trace_zero) t.
  Proof.
    eapply trace_eq_trans;
    [apply trace_plus_comm| apply trace_plus_unitl].
  Qed.


  Theorem trace_plus_unitr_gen t1 t2 :
    trace_eq t1 t2 -> trace_eq (trace_plus t1 trace_zero) t2.
  Proof.
    intros H.
    eapply trace_eq_trans; [ apply trace_plus_unitr | auto].
  Qed.

  Theorem sub_trace_plus_cong tl1 tr1 tl2 tr2 : 
  sub_trace tl1 tl2
  -> sub_trace tr1 tr2
  -> sub_trace (trace_plus tl1 tr1) (trace_plus tl2 tr2).
  Proof.
    unfold sub_trace, trace_plus.
    destruct tl1; destruct tl2; destruct tr1; destruct tr2.
    intros Hl; destruct4 Hl.
    intros Hr; destruct4 Hr.
    split4; apply set_union_subset_cong; auto.
  Qed.

  Theorem trace_proj_reconstruct t 
  : t = Tracing (trace_proj zero t) (trace_proj one t) (trace_proj two t) (trace_proj three t).
  Proof.
    destruct t; reflexivity.
  Qed.

  Theorem sub_trace_In_equiv t1 t2
  : sub_trace t1 t2 
    <-> 
    (forall x tg, set_In x (trace_proj tg t1) -> set_In x (trace_proj tg t2)).
  Proof.
    destruct t1; destruct t2; split.
    intros Hst x tg Hin; destruct4 Hst; destruct tg; eapply subset_In; eassumption.
    intros H; rewrite trace_proj_reconstruct; rewrite trace_proj_reconstruct at 1;
    split4; apply subset_In_def; intros; apply H; assumption.
  Qed.

  Theorem sub_trace_In_util t1 t2 x tg
  : sub_trace t1 t2 
    -> set_In x (trace_proj tg t1)
    -> set_In x (trace_proj tg t2).
  Proof.
    intros Hsub.
    generalize x tg.
    generalize Hsub.
    apply sub_trace_In_equiv.
  Qed.

End Traces.

Hint Resolve trace_eq_refl.
Hint Resolve sub_trace_refl.

Section Enumerates.
  Inductive Enumerates : Enum -> nat -> Value -> Trace -> Prop :=
  | ES_Nat :
      forall n,
        Enumerates E_Nat n (V_Nat n) trace_zero
  | ES_Pair :
      forall l r n ln rn lx rx lt rt,
        Pairing n ln rn ->
        Enumerates l ln lx lt ->
        Enumerates r rn rx rt ->
        Enumerates (E_Pair l r) n (V_Pair lx rx) (trace_plus lt rt)
  | ES_Map :
      forall bi inner inner_x n x t,
        Bijects bi x inner_x ->
        Enumerates inner n inner_x t ->
        Enumerates (E_Map bi inner) n x t
  | ES_Dep:
      forall l f n ln rn lx rx lt rt,
        Pairing n ln rn ->
        Enumerates l ln lx lt ->
        Enumerates (f lx) rn rx rt ->
        Enumerates (E_Dep l f) n (V_Pair lx rx) (trace_plus lt rt)
  | ES_Sum_Left:
      forall l r n ln lx t,
        n = 2 * ln ->
        Enumerates l ln lx t ->
        Enumerates (E_Sum l r) n (V_Sum_Left lx) t
  | ES_Sum_Right:
      forall l r n rn rx t,
        n = 2 * rn + 1 ->
        Enumerates r rn rx t ->
        Enumerates (E_Sum l r) n (V_Sum_Right rx) t
  (* E_Trace hides traces below it. This makes traces super easily spoofable, but makes it easier to reason about when they're not spoofed *)
  | ES_Trace :
      forall n tg e v _t,
        Enumerates e n v _t ->
        Enumerates (E_Trace tg e) n v (trace_one n tg).
  Hint Constructors Enumerates.

  (* Couldn't prove this with traces assumed to be equal. *)
  Theorem Enumerates_to_fun :
    forall e x n1 n2 t1 t2,
      Enumerates e n1 x t1 ->
      Enumerates e n2 x t2 ->
      n1 = n2.
  Proof.
    induction e; intros x n1 n2 t1 t2 E1 E2; inversion E1; inversion E2; subst; try congruence.

    (* E_Pair *)
    - replace lx0 with lx in *; try congruence.
      replace rx0 with rx in *; try congruence.
      erewrite (IHe1 _ _ _ _ _ H2 H10) in *.
      erewrite (IHe2 _ _ _ _ _ H6 H14) in *.
      erewrite (Pairing_from_fun _ _ _ _ H1 H9) in *.
      auto.

    (* E_Map *)
    - erewrite (Bijects_fun_right _ _ _ _ _ _ H1 H8) in *.
      erewrite (IHe _ _ _ _ _ H5 H12) in *.
      auto.

    (* E_Dep *)
    - inversion H13.
      subst.
      erewrite (IHe _ _ _ _ _ H3 H11) in *.
      erewrite (H _ _ _ _ _ _ H7 H15) in *.
      erewrite (Pairing_from_fun _ _ _ _ H2 H10) in *.
      auto.

    (* E_Sum Left *)
    - inversion H10; subst.
      erewrite (IHe1 _ _ _ _ _ H5 H12).
      auto.

    (* E_Sum Right *)
    - inversion H10; subst.
      erewrite (IHe2 _ _ _ _ _ H5 H12).
      auto.

    (* E_Trace *)
    - apply IHe with (x := x) (t1 := _t) (t2 := _t0); assumption.
  Qed.

  Lemma even_fun:
    forall x y,
      2 * x = 2 * y ->
      x = y.
  Proof.
    induction x as [|x]; intros; nliamega.
  Qed.

  Lemma odd_neq_even:
    forall x y,
      2 * x = 2 * y + 1 ->
      False.
  Proof.
    induction x as [|x]; intros; nliamega.
  Qed.

  Lemma odd_fun:
    forall x y,
      2 * x + 1 = 2 * y + 1 ->
      x = y.
  Proof.
    induction x as [|x]; intros; nliamega.
  Qed.

  Theorem Enumerates_from_fun :
    forall e n x1 x2 t1 t2,
      Enumerates e n x1 t1 ->
      Enumerates e n x2 t2 ->
      x1 = x2 /\ t1 = t2.
  Proof.
    induction e; intros x n1 n2 t1 t2 E1 E2; inversion E1; inversion E2; eauto; subst; try congruence.

    (* E_Pair *)
    - erewrite (Pairing_to_l_fun _ _ _ _ _ H1 H9) in *.
      erewrite (Pairing_to_r_fun _ _ _ _ _ H1 H9) in *.
      destruct (IHe1 _ _ _ _ _ H2 H10); subst.
      destruct (IHe2 _ _ _ _ _ H6 H14); subst.
      auto.

    (* E_Map *)
    - destruct (IHe _ _ _ _ _ H5 H12); subst.
      erewrite (Bijects_fun_left _ _ _ _ _ _ H1 H8) in *.
      auto.

    (* E_Dep *)
    - erewrite (Pairing_to_l_fun _ _ _ _ _ H2 H10) in *.
      erewrite (Pairing_to_r_fun _ _ _ _ _ H2 H10) in *.
      destruct (IHe _ _ _ _ _ H3 H11); subst.
      destruct (H _ _ _ _ _ _ H7 H15); subst.
      auto.

    (* E_Sum Left *)
    - erewrite (even_fun _ _ H8) in *.
      destruct (IHe1 _ _ _ _ _ H5 H12); subst.
      auto.

    (* E_Sum Left & Right *)
    - apply odd_neq_even in H8. contradiction.

    (* E_Sum Right & Left *)
    - subst. symmetry in H8. apply odd_neq_even in H8. contradiction.

    (* E_Sum Right *)
    - erewrite (odd_fun _ _ H8) in *.
      destruct (IHe2 _ _ _ _ _ H5 H12); subst.
      auto.

    (* E_Trace *)
    - destruct (IHe _ _ _ _ _ H4 H10); subst.
      auto.
  Qed.

  (* Map/Trace compatibility lemmas *)
  Lemma Enumerates_to_dec_Map :
    forall b e x,
      (forall x,
         { nt: nat * Trace | let (n, t) := nt in Enumerates e n x t }
         + { forall n t, ~ Enumerates e n x t }) ->
      { nt : nat * Trace | let (n, t) := nt in Enumerates (E_Map b e) n x t }
      + { forall n t, ~ Enumerates (E_Map b e) n x t }.
  Proof.
    intros b e x IHe.
    destruct (Bijects_to_dec _ _ b x) as [y B].
    destruct (IHe y) as [[nt IHE] | NIH].

    left. exists nt. destruct nt. eauto.

    right. intros n t E.
    inversion E. subst n0 x0 t0 inner bi.
    rename H1 into B'. rename H5 into IHE.
    erewrite (Bijects_fun_right _ _ _ _ _ _ B B') in *.
    eapply NIH. apply IHE.
  Defined.
  Hint Resolve Enumerates_to_dec_Map.

  Lemma Enumerates_to_dec_Trace :
    forall tg e x,
      (forall x,
         { nt: nat * Trace | let (n, t) := nt in Enumerates e n x t }
         + { forall n t, ~ Enumerates e n x t }) ->
      { nt : nat * Trace | let (n, t) := nt in Enumerates (E_Trace tg e) n x t }
      + { forall n t, ~ Enumerates (E_Trace tg e) n x t }.
  Proof.
    intros tg e x IHe.
    destruct (IHe x) as [[[n t] IHE] | NIH].

    left.
    exists (n, trace_one n tg); eauto.

    right.
    intros n t E.
    inversion E; eapply NIH; eauto.
  Defined.
  Hint Resolve Enumerates_to_dec_Trace.


  Definition Enumerates_to_dec:
    forall e x,
      { nt : nat * Trace | let (n, t) := nt in Enumerates e n x t } + { forall n t, ~ Enumerates e n x t }.
  Proof.
    induction e; destruct x; eauto;
    try ( right; intros _n _t E; inversion E; fail ).

    (* E_Nat *)
    - left; exists (n, trace_zero); constructor.

    (* E_Pair *)
    - rename x1 into lx. rename x2 into rx.
      rename e1 into l. rename e2 into r.
      destruct (IHe1 lx) as [[[ln lt] EL] | LF].
      destruct (IHe2 rx) as [[[rn rt] ER] | RF].
      left.
      destruct (Pairing_to_dec ln rn) as [n P].
      exists (n, trace_plus lt rt).
      eauto.

      right. intros _n _t E; inversion E; subst.
      eapply RF; eauto.

      right. intros _n _t E; inversion E; subst.
      eapply LF; eauto.

    (* E_Dep *)
    - destruct (IHe x1) as [[[ln lt] EL] | LF].
      destruct (X x1 x2) as [[[rn rt] ER] | RF].
      left.
      destruct (Pairing_to_dec ln rn) as [n P].
      exists (n, trace_plus lt rt).
      eauto.

      right. intros _n _t E; inversion E; subst.
      eapply RF; eauto.

      right. intros _n _t E; inversion E; subst.
      eapply LF; eauto.

    (* E_Sum Left *)
    - destruct (IHe1 x) as [[[ln lt] EL] | LF].
      left. exists (2 * ln, lt). eauto.

      right. intros _n _t E. inversion E; subst.
      eapply LF; eauto.

    (* E_Sum Right *)
    - destruct (IHe2 x) as [[[rn rt] ER] | RF].
      left. exists (2 * rn + 1, rt). eauto.

      right. intros _n _t E. inversion E; subst.
      eapply RF; eauto.
  Defined.

  Lemma even_SS :
    forall n,
      { l | n = 2 * l } -> { m | S (S n) = 2 * m }.
  Proof.
    intros n P.
    destruct P.
    exists ((S x)).
    nliamega.
  Defined.

  Lemma odd_SS :
    forall n,
      { r | n = 2 * r + 1 } -> { m | S (S n) = 2 * m + 1 }.
  Proof.
    intros n P.
    destruct P.
    exists ((S x)).
    nliamega.
  Defined.

  Fixpoint even_odd_eq_dec n : { l | n = 2 * l } + { r | n = 2 * r + 1 }.
  Proof.
    refine (match n with
              | 0 => _
              | S 0 => _
              | S (S n') => _
            end).
    left;  exists 0; auto.
    right; exists 0; auto.

    clear n0.
    destruct (even_odd_eq_dec n').
    left; apply even_SS; assumption.
    right; apply odd_SS; assumption.
  Defined.

  Definition Enumerates_from_dec:
    forall e n,
      { xt : Value * Trace | let (x, t) := xt in Enumerates e n x t }.
  Proof.
    induction e; intros n; eauto.

    (* E_Nat *)
    - exists (V_Nat n, trace_zero); eauto.

    (* E_pair *)
    - rename e1 into l. rename e2 into r.
      remember (Pairing_from n) as PF.
      destruct PF as [ln rn].
      destruct (IHe1 ln) as [[lx lt] EL].
      destruct (IHe2 rn) as [[rx rt] ER].
      exists (V_Pair lx rx, trace_plus lt rt).
      eauto.

    (* E_Map *)
    - destruct (IHe n) as [[x t] IHE].
      destruct (Bijects_from_dec _ _ b x) as [y B].
      exists (y, t). eauto.

    (* E_Dep *)
    - rename e into l. rename e0 into f.
      remember (Pairing_from n) as PF.
      destruct PF as [ln rn].
      destruct (IHe ln) as [[lx lt] EL].
      destruct (X lx rn) as [[rx rt] ER].
      exists (V_Pair lx rx, trace_plus lt rt). eauto.

    (* E_Sum *)
    - destruct (even_odd_dec n) as [Hev | Hodd].
      apply even_double in Hev.
      destruct (IHe1 (div2 n)) as [[lx lt] EL].
      exists (V_Sum_Left lx, lt).
      rewrite double_twice in Hev.
      eauto.

      apply odd_double in Hodd.
      destruct (IHe2 (div2 n)) as [[rx rt] ER].
      exists (V_Sum_Right rx, rt).
      rewrite double_twice in Hodd.
      replace (S (2 * div2 n)) with (2 * div2 n + 1) in Hodd by nliamega.
      eauto.

    (* E_Trace *)
    - rename t into tg.
      destruct (IHe n) as [[x _t] E].
      exists (x, trace_one n tg).
      eauto.
  Defined.
End Enumerates.
Hint Constructors Enumerates.
Hint Resolve Enumerates_to_dec_Trace.
Hint Resolve Enumerates_to_dec_Map.


Section EnumTrace.
  Definition Trace_on (e : Enum) (n : nat) : Trace :=
    let (nt, _) := (Enumerates_from_dec e n) in snd nt.

  Fixpoint Trace_lt (e : Enum) n : Trace :=
    match n with
      | 0 => trace_zero
      | S n' => trace_plus (Trace_on e n') (Trace_lt e n')
    end.

  Fixpoint Trace_from_to e lo hi : Trace :=
    if le_lt_dec hi lo
    then trace_zero
    else match hi with
           | 0 => trace_zero
           | S hi' => trace_plus (Trace_on e hi') (Trace_from_to e lo hi')
         end.

  Theorem trace_lt_from_to_0_same e n : trace_eq (Trace_lt e n) (Trace_from_to e 0 n).
  Proof.
    induction n.
    simpl.
    split4; apply set_eq_refl.

    simpl.
    unfold trace_plus.
    destruct (Trace_on e n).
    destruct (Trace_lt e n).
    destruct (Trace_from_to e 0 n).
    destruct4 IHn.
    split4; (apply set_union_cong; [apply set_eq_refl|]; auto).
  Qed.

  Theorem trace_from_to_ge e m n
  : n <= m ->
    Trace_from_to e m n = trace_zero.
  Proof.
    intros H.
    unfold Trace_from_to.
    remember (le_lt_dec n m) as l.
    destruct l; [| apply False_ind; nliamega ].
    destruct n; rewrite <-Heql; reflexivity.
  Qed.

  Theorem trace_from_to_self e m 
  : Trace_from_to e m m = trace_zero.
  Proof. apply trace_from_to_ge; nliamega. Qed.

  Theorem trace_from_to_split1r e m n
  : m <= n ->
    trace_eq (Trace_from_to e m (S n))
             (trace_plus (Trace_from_to e m n) (Trace_on e n)).
  Proof.
    intros H.
    unfold Trace_from_to at 1.
    remember (le_lt_dec (S n) m).
    destruct s.
    assert (S n <= n).
    apply le_trans with (m := m); auto.
    apply le_Sn_n in H0.
    contradiction.
    fold Trace_from_to.
    apply trace_plus_comm.
  Qed.

  Theorem trace_from_to_split1l' e m n
  : trace_eq (Trace_from_to e m (S (m + n)))
             (trace_plus (Trace_on e m) (Trace_from_to e (S m) (S (m + n)))).
  Proof.
    generalize dependent m.
    induction n as [| n].
    intros m.
    replace (S (m + 0)) with (S m) by nliamega.
    unfold Trace_from_to at 1.
    remember (le_lt_dec (S m) m) as t.
    destruct t.
    clear Heqt.
    apply le_Sn_n in l.
    contradiction.

    fold Trace_from_to.
    rewrite trace_from_to_self.
    rewrite trace_from_to_self.
    apply trace_eq_refl.
    intros m.
    unfold Trace_from_to.
    remember (le_lt_dec (S (m + S n)) m) as t.
    destruct t.
    assert (m < (S (m + S n))) by nliamega.
    clear Heqt.
    apply (le_not_gt) in l.
    contradiction.
    fold Trace_from_to.
    clear l Heqt.
    remember (le_lt_dec (S (m + S n)) (S m)).
    destruct s.
    assert ((S (m + S n)) > S m) by nliamega.
    clear Heqs; apply le_not_gt in l; contradiction.
    replace (m + S n) with (S (m + n)) by nliamega.
    eapply trace_eq_trans.
    apply trace_plus_cong; [apply trace_eq_refl | apply IHn ].
    eapply trace_eq_trans.
    apply trace_plus_assoc.
    eapply trace_eq_trans.
    apply trace_plus_cong.
    apply trace_plus_comm.
    apply trace_eq_refl.
    eapply trace_eq_trans.
    apply trace_eq_symm.
    apply trace_plus_assoc.
    apply trace_eq_refl.
  Qed.

  Theorem trace_from_to_split1l e m n
  : m < n ->
    trace_eq (Trace_from_to e m n)
             (trace_plus (Trace_on e m) (Trace_from_to e (S m) n)).
  Proof.
    intros H.
    remember (pred (n - m)) as t.
    assert (n = (S (m + t))) by nliamega.
    subst n.
    apply trace_from_to_split1l'.
  Qed.


  Theorem trace_from_to_split e m n p :
    (m <= n < p)
    -> trace_eq (Trace_from_to e m p)
                (trace_plus (Trace_from_to e m n)
                            (Trace_from_to e n p)).
  Proof.
    generalize dependent p.
    generalize dependent m.

    induction n.
    intros m p [Hmzero Hppos].
    apply le_n_0_eq in Hmzero; subst.
    remember (Trace_from_to e 0 0).
    simpl in Heqt; subst.
    apply trace_eq_symm.
    apply trace_plus_unitl.

    intros m p [Hmn Hp].
    inversion Hmn; subst.
    clear Hmn.
    apply trace_eq_symm.
    rewrite (trace_from_to_self e (S n)).
    apply trace_plus_unitl_gen.
    apply trace_eq_refl.

    apply trace_eq_trans with (t2:= (trace_plus (Trace_from_to e m n) (Trace_from_to e n p)));
      [apply IHn; nliamega| ].
    apply trace_eq_trans with (t2 := (trace_plus (Trace_from_to e m n)
                                                 (trace_plus (Trace_on e n)
                                                             (Trace_from_to e (S n) p)))).
    apply trace_plus_cong; [apply trace_eq_refl| ].
    apply trace_from_to_split1l; nliamega.

    eapply trace_eq_trans.
    apply trace_plus_assoc.
    apply trace_plus_cong; [| apply trace_eq_refl].
    apply trace_eq_symm.
    apply trace_from_to_split1r; nliamega.
  Qed.

  Theorem trace_from_to_0_split :
    forall m n e,
      m < n ->
      trace_eq (Trace_lt e n)
               (trace_plus (Trace_lt e m)
                           (Trace_from_to e m n)).
  Proof.
    intros m n e Hmn.
    eapply trace_eq_trans.
    apply trace_lt_from_to_0_same.
    eapply trace_eq_trans.
    apply trace_from_to_split with (n := m); split; [nliamega | assumption].
    apply trace_plus_cong.
    apply trace_eq_symm.
    apply trace_lt_from_to_0_same.
    apply trace_eq_refl.
  Qed.

  Theorem Trace_nat n tg : Trace_on (E_Trace tg E_Nat) n = trace_one n tg.
  Proof.
    unfold Trace_on.
    destruct (Enumerates_from_dec _ _) as [[v t] Henum].
    inversion Henum; subst.
    reflexivity.
  Qed.

  Theorem trace_off tg1 tg2 n : tg1 <> tg2 -> trace_proj tg2 (Trace_on (E_Trace tg1 E_Nat) n) = empty_set'.
  Proof.
    rewrite Trace_nat.
    compute.
    destruct tg1; destruct tg2; intuition.
  Qed.

  Theorem trace_proj_plus_distrl tg t1 t2
  : trace_proj tg (trace_plus t1 t2) = (set_union' (trace_proj tg t1) (trace_proj tg t2)).
  Proof.
    destruct t1; destruct t2; destruct tg; auto.
  Qed.

  Theorem Trace_on_correct e n x t : Enumerates e n x t -> Trace_on e n = t.
  Proof.
    intros H.
    unfold Trace_on.
    destruct (Enumerates_from_dec e n) as [[v tgaf] Henum].
    simpl.
    destruct (Enumerates_from_fun _ _ _ _ _ _ H Henum); auto.
  Qed.

  Theorem trace_lt_Nat n tg
  : set_eq (z_to_n n)
           (trace_proj tg (Trace_lt (E_Trace tg E_Nat) n)).
  Proof.
    induction n as [| n IHn]; [destruct tg; compute; tauto|].
    unfold Trace_lt. fold Trace_lt.
    unfold z_to_n. fold z_to_n.
    rewrite trace_proj_plus_distrl.
    rewrite Trace_nat.
    eapply set_eq_trans.
    apply set_eq_symm. apply set_add_cons_eq.
    eapply set_eq_trans.
    replace (n :: z_to_n n) with ((n :: nil) ++ z_to_n n) by reflexivity.
    apply set_eq_symm; apply set_union_app_eq.
    apply set_union_cong; auto.
    destruct tg; compute; tauto.
  Qed.

  Theorem trace_lt_Nat_off n tg1 tg2
  : tg1 <> tg2 ->
    (trace_proj tg1 (Trace_lt (E_Trace tg2 E_Nat) n)) = nil.
  Proof.
    intros Hdiff.
    induction n.
    destruct tg1; auto.
    unfold Trace_lt; fold Trace_lt.
    rewrite trace_proj_plus_distrl.
    rewrite trace_off.
    rewrite IHn; compute; auto.
    auto.
  Qed.

  Lemma sub_trace_from_tol l m n e
  : l <= m
    -> sub_trace (Trace_from_to e m n) (Trace_from_to e l n).
  Proof.
    intros H; remember (m - l) as k; replace m with (l + k) by nliamega; clear dependent m.
    induction k.
    replace (l + 0) with l by nliamega; apply sub_trace_refl.
    eapply sub_trace_trans; [| apply IHk].
    destruct (le_dec n (l + S k)).
    rewrite trace_from_to_ge by assumption;
      apply sub_trace_zero.
    eapply sub_trace_trans;
      [| apply trace_eq_weakenl; apply trace_eq_symm; apply trace_from_to_split with (n := l + S k); nliamega ];
      apply sub_trace_plus_transr; apply sub_trace_refl.
  Qed.

  Theorem sub_trace_from_to l m n p e
  : l <= m
    -> n <= p
    -> sub_trace (Trace_from_to e m n) (Trace_from_to e l p).
  Proof.
    intros Hlm Hnp.
    remember (p - n) as k; replace p with (n + k) by nliamega; clear dependent p.
    induction k.
    replace (n+0) with n by nliamega; apply sub_trace_from_tol; auto.
    replace (n + S k) with (S (n + k)) by nliamega.
    unfold Trace_from_to at 2.
    remember (le_lt_dec (S (n + k)) l) as Hlelt.
    destruct Hlelt.
    replace (Trace_from_to e l (n + k)) with trace_zero in IHk; auto.
    symmetry.
    apply trace_from_to_ge; nliamega.
    fold Trace_from_to.
    apply sub_trace_plus_transr; auto.
  Qed.

  Theorem trace_from_to_Nat_off m n tg1 tg2
  : tg1 <> tg2 ->
    (trace_proj tg1 (Trace_from_to (E_Trace tg2 E_Nat) m n)) = empty_set'.
  Proof.
    intros Hdiff.
    assert (sub_trace (Trace_from_to (E_Trace tg2 E_Nat) m n) (Trace_lt (E_Trace tg2 E_Nat) n)).
    eapply sub_trace_trans.
    apply sub_trace_from_to with (l := 0) (p := n); try nliamega.
    apply trace_eq_weakenl; apply trace_eq_symm; apply trace_lt_from_to_0_same.
    apply subset_nil_nil.
    erewrite <-trace_lt_Nat_off; [ apply sub_trace_proj|]; eauto.
  Qed.

  Theorem trace_on_Pair_off tg e1 e2 m
  : (forall n, trace_proj tg (Trace_on e1 n) = empty_set')
    -> (forall n, trace_proj tg (Trace_on e2 n) = empty_set')
    -> trace_proj tg (Trace_on (E_Pair e1 e2) m) = empty_set'.
  Proof.
    intros.
    unfold Trace_on.
    destruct (Enumerates_from_dec _ _) as [[v t] Henum].
    inversion Henum; subst.
    apply Trace_on_correct in H4.
    apply Trace_on_correct in H8.
    simpl.
    subst.
    rewrite trace_proj_plus_distrl.
    rewrite H, H0.
    trivial.
  Qed.

  Theorem trace_lt_Pair_off tg e1 e2 m
  : (forall n, trace_proj tg (Trace_on e1 n) = empty_set')
    -> (forall n, trace_proj tg (Trace_on e2 n) = empty_set')
    -> trace_proj tg (Trace_lt (E_Pair e1 e2) m) = empty_set'.
  Proof.
    induction m; [intros; destruct tg; reflexivity|].
    intros H1 H2.
    unfold Trace_lt; fold Trace_lt.
    rewrite trace_proj_plus_distrl.
    apply subset_nil_nil.
    apply subset_union_both.
    rewrite trace_on_Pair_off; [apply subset_refl| |]; auto.
    rewrite IHm; auto.
  Qed.

  Theorem set_In_trace' (tg : tag) e x m n :
    set_In x (trace_proj tg (Trace_from_to e m (S (m + n))))
    <->
    (exists k,
       m <= k < S (m + n) /\ set_In x (trace_proj tg (Trace_on e k))).
  Proof.
    split.
    generalize dependent m.
    induction n; intros m;
    [
      replace (S (m + 0)) with (S m) by nliamega;
      destruct tg;
      (intros H; exists m; split; [nliamega |];
                        unfold Trace_from_to in H;
                        destruct (le_lt_dec (S m) m);
                        [apply le_Sn_n in l; contradiction
                        |
                        fold Trace_from_to in H;
                          rewrite trace_from_to_self in H;
                          remember (trace_plus (Trace_on e m) trace_zero) as t;
                          destruct t;
                          simpl in *;
                          remember (Trace_on e m) as t';
                          destruct t';
                          simpl in *;
                          inversion Heqt; subst; auto ])
    | unfold Trace_from_to; fold Trace_from_to;
      destruct (le_lt_dec (S (m + S n)) m) as [contra | _]; [ assert (~ (S (m + S n)) <= m) by (apply gt_not_le; nliamega); contradiction|];
      unfold trace_plus;
      remember (Trace_on e (m + S n))as t; destruct t as [tl tr];
      remember (Trace_from_to e m (m + S n)) as t; destruct t as [t0' t1' t2' t3'];
      replace (m + S n) with (S (m + n)) in * by nliamega;
      destruct tg;
      (simpl; intros Hin_union;
       destruct (set_union_elim eq_nat_dec _ _ _ Hin_union);
       [exists (S (m + n)); split; [nliamega|]; destruct Heqt; auto |]);
      [ replace t0' with (trace_proj zero  (Trace_from_to e m (S (m + n)))) in H by (rewrite <-Heqt0; auto)
      | replace t1' with (trace_proj one   (Trace_from_to e m (S (m + n)))) in H by (rewrite <-Heqt0; auto)
      | replace t2' with (trace_proj two   (Trace_from_to e m (S (m + n)))) in H by (rewrite <-Heqt0; auto)
      | replace t3' with (trace_proj three (Trace_from_to e m (S (m + n)))) in H by (rewrite <-Heqt0; auto)
      ];
      (destruct (IHn m H) as [k [Hless Hinn]]; exists k; (split; [nliamega | auto]))].

    intros [k [[Hmk HkSmn] Hin]];
      induction n as [| n].
    replace (S (m + 0)) with (S m) in * by nliamega;
      unfold Trace_from_to;
      destruct (le_lt_dec (S m) m); [apply le_Sn_n in l; contradiction|];
      fold Trace_from_to; rewrite trace_from_to_self; assert (k = m) by nliamega; subst;

      remember (trace_plus (Trace_on e m) trace_zero) as t;
      destruct t; simpl in *;
      remember (Trace_on e m) as t';
      destruct t';
      simpl in *;
      inversion Heqt; subst; auto.

    replace (S (m + n)) with (m + S n) in * by nliamega;
      destruct (eq_nat_dec k (m + S n)); subst;
      unfold Trace_from_to; fold Trace_from_to;
      (destruct (le_lt_dec (S (m + S n)) m); [ assert (~ (S (m + S n) <= m)) by (apply le_not_gt; nliamega); contradiction| ]); (remember (Trace_on e (m + S n)) as t); destruct t as [t0 t1 t2 t3];
      (remember (Trace_from_to e m (m + S n)) as t'); destruct t' as [t0' t1' t2' t3'].
    destruct tg; (
        simpl in *; apply set_union_intro1; auto).

    destruct tg; simpl in *; apply set_union_intro2; apply IHn; nliamega.
  Qed.

  Theorem set_In_Trace_from_to (tg : tag) e x m n :
    (m < n) ->
    (set_In x (trace_proj tg (Trace_from_to e m n)) <->
     (exists k,
        m <= k < n /\ set_In x (trace_proj tg (Trace_on e k)))).
  Proof.
    intros H.
    remember (pred (n - m)) as p.
    assert (n = (S (m + p))) by nliamega.
    subst n.
    apply set_In_trace'.
  Qed.

  Theorem set_In_Trace_lt tg e x n :
    set_In x (trace_proj tg (Trace_lt e (S n)))
    <->
    exists k,
      k < S n /\ set_In x (trace_proj tg (Trace_on e k)).
  Proof.
    destruct (set_In_Trace_from_to tg e x 0 (S n)) as [Hl Hr]; try nliamega.
    split; [clear Hr|clear Hl].
    intros Hin.
    assert (set_In x (trace_proj tg (Trace_from_to e 0 (S n)))).
    apply In_subset_def with (trace_proj tg (Trace_lt e (S n))); [| assumption].
    apply sub_trace_proj; apply trace_eq_weakenl; apply trace_lt_from_to_0_same.
    destruct (Hl H) as [k [? Hink]].
    exists k; split; [nliamega| assumption].
    
    intros Hex; destruct Hex as [k [Hbound Hink]].
    assert (set_In x (trace_proj tg (Trace_from_to e 0 (S n)))).
    apply Hr.
    exists k; split; [nliamega| assumption].
    apply In_subset_def with (trace_proj tg (Trace_from_to e 0 (S n))); [| assumption].
    apply sub_trace_proj; apply trace_eq_weakenr; apply trace_lt_from_to_0_same.
  Qed.

  Theorem sub_trace_plus_introl t1 t2 t3
  : sub_trace t1 t2 -> sub_trace t1 (trace_plus t2 t3).
  Proof.
    unfold sub_trace, trace_plus; destruct t1, t2, t3.
    intros H; destruct H as [H1 [H2 [H3 H4]]].
    Local Hint Resolve subset_union_transl.
    split4; auto.
  Qed.

  Theorem sub_trace_plus_intror t1 t2 t3
  : sub_trace t1 t3 -> sub_trace t1 (trace_plus t2 t3).
  Proof.
    unfold sub_trace, trace_plus; destruct t1, t2, t3.
    intros H; destruct H as [H1 [H2 [H3 H4]]].
    Local Hint Resolve subset_union_transr.
    split4; auto.
  Qed.

  Theorem Trace_from_to_sub' e m n p : sub_trace (Trace_from_to e m n) (Trace_from_to e m (n + p)).
  Proof.
    induction p.
    replace (n + 0) with n by nliamega; apply sub_trace_refl.
    replace (n + S p) with (S (n + p)) by nliamega.
    unfold Trace_from_to at 2; fold Trace_from_to.
    destruct (le_lt_dec (S (n + p))).
    replace (Trace_from_to e m n) with trace_zero; [apply sub_trace_refl|].
    unfold Trace_from_to.
    destruct n.
    destruct (le_lt_dec 0 m); auto.
    destruct (le_lt_dec (S n) m); auto; nliamega.
    apply sub_trace_plus_intror; auto.
  Qed.

  Theorem Trace_from_to_sub e m n p : n <= p -> sub_trace (Trace_from_to e m n) (Trace_from_to e m p).
  Proof.
    Local Hint Resolve Trace_from_to_sub'.
    intros; replace p with (n + (p - n)) by nliamega; auto.
  Qed.

  Theorem Trace_lt_sub e m n : m <= n -> sub_trace (Trace_lt e m) (Trace_lt e n).
  Proof.
    intros H.
    eapply sub_trace_trans; [apply trace_eq_weakenl; apply trace_lt_from_to_0_same| ].
    eapply sub_trace_trans; [| apply trace_eq_weakenr; apply trace_lt_from_to_0_same].
    apply Trace_from_to_sub; auto.
  Qed.

  Theorem Trace_lt_Enumerates m n e v t 
  : m < n
    -> Enumerates e m v t
    -> sub_trace t (Trace_lt e n).
  Proof.
    intros Hmn Enum.
    destruct n; [ nliamega|].
    apply sub_trace_In_equiv.
    intros x tg Hin.
    apply set_In_Trace_lt.
    exists m; split; auto.
    unfold Trace_on.
    destruct (Enumerates_from_dec _ _) as [[v' t'] Henum].
    simpl.
    destruct (Enumerates_from_fun _ _ _ _ _ _ Enum Henum); subst; assumption.
  Qed.

End EnumTrace.

Section Fairness.
  Definition Fair2 (k : Enum -> Enum -> Enum) :=
    forall n,
    exists equilibrium,
      match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat)) equilibrium with
        | Tracing l_uses r_uses _ _ =>
          n < equilibrium /\ set_eq  l_uses r_uses
      end.

  Definition Fair3 (k : Enum -> Enum -> Enum -> Enum) :=
    forall n,
    exists equilibrium,
      match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)) equilibrium with
        | Tracing z_uses o_uses t_uses _ =>
          n < equilibrium /\ set_eq z_uses o_uses /\ set_eq o_uses t_uses
      end.

  Definition Fair4 (k : Enum -> Enum -> Enum -> Enum -> Enum) :=
    forall n,
    exists equilibrium,
      match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat) (E_Trace three E_Nat)) equilibrium with
        | Tracing z_uses o_uses tw_uses th_uses =>
          n < equilibrium /\ set_eq z_uses o_uses /\ set_eq o_uses tw_uses /\ set_eq tw_uses th_uses
      end.

  Definition AltUnfair3 k :=
    exists threshold,
      forall eq_cand,
        eq_cand > threshold ->
        match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)) eq_cand with
          | Tracing use0 use1 use2 _ =>
            (~ (set_eq use0 use1)) \/ (~ (set_eq use1 use2)) \/ (~ (set_eq use0 use2))
        end.

  Theorem AltUnfair3Suff k : AltUnfair3 k -> ~ (Fair3 k).
  Proof.
    unfold AltUnfair3, Fair3, not.
    intros [thresh Halt] Hunf.
    destruct (Hunf thresh) as [eq_cand Hblah].
    clear Hunf.
    remember (Halt eq_cand).
    clear Halt Heqy.
    destruct (Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat))
                       eq_cand) as [t0 t1 t2 t3] in *.
    intuition.
    assert (set_eq t0 t2) by (eapply set_eq_trans; eauto); contradiction.
  Qed.
  
  Section SumFair.
    Lemma Sum_Parity_Trace :
      forall n,
        Trace_on (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) n
        = trace_one (div2 n)
                    (if even_odd_dec n
                     then zero
                     else one).
    Proof.
      intros n.
      remember (even_odd_dec n) as mH.
      unfold Trace_on; simpl.
      destruct mH; rewrite <-HeqmH; auto.
    Qed.

    Lemma Sum_precise
    : forall n e1 e2,
        trace_eq (Trace_lt (E_Sum e1 e2) (double n))
                 (trace_plus (Trace_lt e1 n)
                             (Trace_lt e2 n)).
    Proof.
      intros n e1 e2.
      induction n.
      compute; tauto.
      rewrite double_S.
      unfold Trace_lt at 1; fold Trace_lt.
      unfold Trace_on.
      remember (Enumerates_from_dec (E_Sum e1 e2) (S (double n))) as Er; destruct Er as [[vr tr] Er].
      remember (Enumerates_from_dec (E_Sum e1 e2) (double n)) as El; destruct El as [[vl tl] El].
    Admitted.
    

    (* Proof idea: equilibrium = 2 * n + 2,  uses = 0..(S n) *)
    Theorem Sum_Fair : Fair2 E_Sum.
    Proof.
      unfold Fair2.
      intros n.
      exists (2 * n + 2).
      remember (Trace_lt (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (2 * n + 2)).
      destruct t as [tz to ttw tth].
      split; [nliamega| ].

      generalize dependent tth.
      generalize dependent ttw.
      generalize dependent to.
      generalize dependent tz.
      induction n.
      intros tz to ttw tth Heqt.
      inversion Heqt; auto; apply set_eq_refl.

      intros tz to ttw tth Htzto.
      remember (Trace_lt (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (2 * n + 2)).
      replace (2 * S n + 2) with (S (S (2 * n + 2))) in Htzto by nliamega.
      simpl in Htzto.
      replace (n + (n + 0) + 2) with (2 * n + 2) in Htzto by nliamega.
      destruct t as [tz' to' ttw' tth'].
      assert (set_eq tz' to').
      eapply IHn ; auto.
      rewrite <-Heqt in Htzto.
      clear Heqt.
      clear IHn.
      replace (Trace_on (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (S (2 * n + 2))) with (trace_one (S n) one) in Htzto.

      replace (Trace_on (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) ((2 * n)+2)) with (trace_one (S n) zero) in Htzto.
      unfold trace_one in Htzto.
      unfold trace_plus in Htzto.
      inversion Htzto.
      clear  Htzto H1 H2.

      - apply set_eq_trans with (s2 := set_union' (S n :: nil) tz').
        apply set_union_unitl.
        apply set_eq_trans with (s2 := set_union' (S n :: nil) to').
        apply set_union_cong; auto.
        apply set_union_cong.
        apply set_eq_refl.
        apply set_eq_symm.
        apply set_union_unitl.

      (* Trace (left + right) (2n+3) =  *)
      - unfold Trace_on.
        destruct (Enumerates_from_dec (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (2 * n + 2)).
        assert (Enumerates (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (2 * n + 2) (V_Sum_Left (V_Nat (S n))) (trace_one (S n) zero)).
        apply ES_Sum_Left with (ln := (S n)); [nliamega| ].
        econstructor.
        constructor.
        destruct x.

        destruct (Enumerates_from_fun _ _ _ _ _ _ y H0); subst.
        auto.

      - unfold Trace_on.
        destruct (Enumerates_from_dec (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (S (2 * n + 2))).
        assert (Enumerates (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (S (2 * n + 2)) (V_Sum_Right (V_Nat (S n))) (trace_one (S n) one)).
        apply ES_Sum_Right with (rn := S n); [nliamega|].
        econstructor; constructor.
        destruct x.
        destruct (Enumerates_from_fun _ _ _ _ _ _ y H0); subst.
        auto.
    Qed.

  End SumFair.

  Section NaiveSumUnfair.
    Definition NaiveSum3 e1 e2 e3 :=
      E_Sum e1 (E_Sum e2 e3).

    Definition foo n :=
      let p := (S (div2 (S (div2 n))))
      in let m := S p
         in (2 * m, n, 4 * p).
    Eval compute in map foo (6::7::8::9::10::11::12::13::nil).

    Lemma div2_slower_than_id n :
      4 <= n ->
      (S (div2 (S n))) < n.
    Proof.
      intros H.
      remember (n - 4) as k; replace n with (4 + k) by nliamega; clear dependent n; rename k into n.
      induction n.
      compute; nliamega.
      destruct (even_odd_dec (S (4 + n))).
      rewrite even_div2 in IHn by assumption.
      replace (S (4 + S n)) with (S (S (4 + n))) by nliamega.
      nliamega.

      replace (S (4 + n)) with (4 + S n) in o by nliamega.
      rewrite <-odd_div2 by assumption.
      replace (4 + S n) with (S (4 + n)) at 1 by nliamega.
      nliamega.
    Qed.

    Definition x4 n := double (double n).
    
    Lemma par4 : forall n, (n = x4 (div2 (div2 n)) /\ even n /\ even (div2 n))
                           \/ (n = (x4 (div2 (div2 n))) + 1 /\ odd n /\ even (div2 n))
                           \/ (n = (x4 (div2 (div2 n))) + 2 /\ even n /\ odd (div2 n))
                           \/ (n = (x4 (div2 (div2 n))) + 3 /\ odd n /\ odd (div2 n)).
    Proof.
      intros.
      destruct (even_odd_dec n).
      - remember (even_div2 n e).
        destruct (even_odd_dec (div2 n)).
        + left; split; [| split]; try assumption.
          unfold x4.
          rewrite <-even_double by assumption.
          apply even_double; assumption.
        + right; right; left; split; [| split]; try assumption.
          unfold x4.
          replace (double (double (div2 (div2 n))) + 2) with (S (S (double (double (div2 (div2 n)))))) by nliamega.
          rewrite <-double_S.
          rewrite <-odd_double by assumption.
          apply even_double; assumption.
      - destruct (even_odd_dec (div2 n)).
        + right; left; split; [| split]; try assumption.
          unfold x4.
          rewrite <-even_double by assumption.
          replace (double (div2 n) + 1) with (S (double (div2 n))) by nliamega.
          apply odd_double; assumption.
        + right; right; right; split; [| split]; try assumption.
          unfold x4.
          replace (double (double (div2 (div2 n))) + 3) with (S (S (S (double (double (div2 (div2 n))))))) by nliamega.
          rewrite <-double_S.
          rewrite <-odd_double by assumption.
          apply odd_double; assumption.
    Qed.

    Lemma div2div4 : forall n, n >= 8 -> exists m p, 2 * m <= n < 4 * p /\ p < m.
    Proof.
      intros n Hn4.
      remember (S (div2 (S (div2 n)))) as p.
      remember (S p) as m.
      exists m.
      exists p.
      split; [| nliamega].
      subst.
      replace (4 * _) with (2 * (2 * (S (div2 (S (div2 n)))))) by nliamega.
      repeat (rewrite <-double_twice).
      destruct (par4 n) as [[? [? ?]] | [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]]; rewrite H at 2; rewrite H at 3; unfold x4.
      - clear H0; split.
        + rewrite double_twice; rewrite double_twice.
          apply mult_le_compat_l.
          rewrite <-even_div2 by assumption.
          unfold double.
          assert (div2 (div2 n) >= 2) by admit.
          nliamega.
        + rewrite <-even_div2 by assumption.
          unfold x4 in H.
          (repeat (rewrite double_twice)).
          nliamega.
      - split.
        + rewrite double_S.
          replace (double (double (div2 (div2 n))) + 1 ) with (S (double (double (div2 (div2 n))))) by nliamega.
          apply le_n_S.
          rewrite <-even_div2 by assumption.
          assert (div2 (div2 n) >= 2) by admit.
          unfold double.
          nliamega.
        + rewrite <-even_div2 by assumption.
          replace (_ + 1) with (S (double (double (div2 (div2 n))))) by nliamega.
          unfold double; nliamega.
      - admit.
      - admit.
    Qed.

    Lemma SumSum_precise
    : forall n e1 e2 e3,
        trace_eq (Trace_lt (E_Sum e1 (E_Sum e2 e3)) (double (double n)))
                 (trace_plus (Trace_lt e1 (double n))
                             (trace_plus (Trace_lt e2 n)
                                         (Trace_lt e3 n))).
    Admitted.

    Definition NS3T := NaiveSum3 (E_Trace zero E_Nat)
                                 (E_Trace one  E_Nat)
                                 (E_Trace two  E_Nat).

    Lemma NS3Tl_precise
    : forall n,
        set_eq (trace_proj zero (Trace_lt NS3T (double n)))
               (z_to_n n).
    Proof.
    Admitted.

    Lemma NS3Tr_precise
    : forall n,
        set_eq (trace_proj one (Trace_lt NS3T (double (double n))))
               (z_to_n n).
    Admitted.

    Theorem NaiveSumUnfair : ~ (Fair3 NaiveSum3).
    Proof.
      apply AltUnfair3Suff; unfold AltUnfair3; fold NS3T.
      exists 7.
      intros n H.
      remember (Trace_lt NS3T n) as t; destruct t as [s0 s1 s2 s4].
      assert (exists m p, 2 * m <= n < 4 * p /\ p < m) as [m [p [[Hmn Hnp] Hpn]]] by (apply div2div4; nliamega).
      left.
      
      assert (~ subset s0 s1); [| intros [? ?]; contradiction ].

      assert (subset (z_to_n m) s0).
      rewrite <-double_twice in *.
      replace s0 with (trace_proj zero (Trace_lt NS3T n)) by (rewrite <-Heqt; trivial).
      eapply subset_trans; [| apply sub_trace_proj; apply Trace_lt_sub; apply Hmn ].
      apply set_subset_weaken; apply set_eq_symm; apply NS3Tl_precise.
      
      assert (subset s1 (z_to_n p)).
      replace (4 * p) with (double (double p)) in * by (simpl; unfold double; nliamega).
      replace s1 with (trace_proj one (Trace_lt NS3T n)) by (rewrite <-Heqt; trivial).
      eapply subset_trans.
      apply sub_trace_proj.
      apply Trace_lt_sub with (n := double (double p)); nliamega.
      apply set_subset_weaken.
      apply NS3Tr_precise.
      
      intros Hcontra.
      eapply z_to_n_nosub; [apply Hpn|].
      repeat (eapply subset_trans; [eassumption|]); apply subset_refl.
    Qed.
  End NaiveSumUnfair.

  Section PairFair.
    Definition E_PairNN := (E_Pair (E_Trace zero E_Nat) (E_Trace one E_Nat)).
    Lemma Pair_layer e1 e2 n
    : trace_eq (Trace_from_to (E_Pair e1 e2) (n * n) (S n * S n))
               (trace_plus (Trace_lt e1 (S n)) (Trace_lt e2 (S n))).
    Proof.
      apply trace_eq_eq'_equiv; split.
      (* trace (e1 x e2) n^2 (n+1)^2 < (trace ) *)
      (* This one needs some serious infrastructure *)
      - apply sub_trace_In_equiv; intros x tg Hin;
        rewrite set_In_Trace_from_to in Hin by nliamega; destruct Hin as [k [[Hnnk HkSnSn] Hin]].
        unfold Trace_on in Hin.
        destruct (Enumerates_from_dec (E_Pair e1 e2) k) as [[v t] Henum].
        inversion Henum; subst.
        simpl in Hin.
        destruct (sub_trace_In_equiv (trace_plus lt rt)
                                     (trace_plus (Trace_lt e1 (S n)) (Trace_lt e2 (S n)))).
        apply H; [| assumption].
        clear H H0.
        apply sub_trace_plus_cong;
          eapply Trace_lt_Enumerates; [| eassumption | | eassumption];
          destruct (Pairing_bound ln rn k n); auto.
      - eapply sub_trace_trans; [|apply trace_eq_weakenl; apply sub_trace_plus_eq; apply sub_trace_refl];
        apply sub_trace_plus_cong.
        (* trace e1 0..n+1 < trace (e1 x e2) n^2 (n+1)^2 *)
        + apply sub_trace_In_equiv; intros x tg Hin;
          rewrite set_In_Trace_lt in Hin by nliamega;
          destruct Hin as [k [Hkn Hin]];
          apply set_In_Trace_from_to; [nliamega|].
          destruct (le_lt_dec n k);
            [exists (k*k + k + n) | exists (k + n * n)];
            (split; [nliamega|]);
            unfold Trace_on; destruct (Enumerates_from_dec _ _) as [[v t] Henum];
            inversion Henum; subst; simpl; 
            rewrite trace_proj_plus_distrl; apply set_union_intro1;
            [ assert (Pairing (k * k + k + n) k n) by (constructor; nliamega)
            | assert (Pairing (k + n * n) k n) by (constructor; nliamega)];
            destruct (Pairing_to_fun _ _  _ _ _ H1 H); subst;
            (erewrite Trace_on_correct in Hin; eassumption).
        + apply sub_trace_In_equiv; intros x tg Hin;
          rewrite set_In_Trace_lt in Hin by nliamega;
          destruct Hin as [k [Hkn Hin]];
          apply set_In_Trace_from_to; [nliamega|].
          destruct (le_lt_dec k n);
            [exists (n * n + n + k) | exists (n + k * k)]; (split; [nliamega|]);
            unfold Trace_on; destruct (Enumerates_from_dec _ _) as [[v t] Henum];
            inversion Henum; subst; simpl; 
            rewrite trace_proj_plus_distrl; apply set_union_intro2;
            [ assert (Pairing (n * n + n + k) n k) by (constructor; nliamega)
            | assert (Pairing (n + k * k) n k) by (constructor; nliamega) ];
            destruct (Pairing_to_fun _ _  _ _ _ H1 H); subst;
            (erewrite Trace_on_correct in Hin; eassumption).
    Qed.

    Lemma PairNN_layer :
      forall n,
        trace_eq (Trace_from_to E_PairNN (n * n) (S n * S n))
                 (Tracing (z_to_n (S n)) (z_to_n (S n)) empty_set' empty_set').
    Proof.
      intros n.
      eapply trace_eq_trans.
      unfold E_PairNN; apply Pair_layer.
      apply trace_eq_symm.
      apply trace_eq_trans with (trace_plus (Tracing (z_to_n (S n)) empty_set' empty_set' empty_set')
                                            (Tracing empty_set' (z_to_n (S n)) empty_set' empty_set')).
      remember (S n) as k; unfold trace_plus; split4; auto; apply set_eq_symm; apply set_union_unitl.
      apply trace_plus_cong; rewrite trace_proj_reconstruct.
      split4; [ apply trace_lt_Nat | | | ]; rewrite trace_lt_Nat_off by discriminate; auto.
      split4; [ | apply trace_lt_Nat | | ]; rewrite trace_lt_Nat_off by discriminate; auto.
    Qed.      

    Lemma Pair_precise
    : forall n e1 e2,
        trace_eq (Trace_lt (E_Pair e1 e2) (n * n))
                 (trace_plus (Trace_lt e1 n)
                             (Trace_lt e2 n)).
      intros n.
      induction n as [| n IHn]; [  intros; compute; tauto| ].
      intros e1 e2.
      eapply trace_eq_trans.
      apply trace_from_to_0_split with (m := n * n) (n := S n * S n); nliamega.
      eapply trace_eq_trans; [apply sub_trace_plus_eq| apply Pair_layer].
      eapply sub_trace_trans; [| apply trace_eq_weakenl; apply trace_eq_symm; apply Pair_layer ].
      eapply sub_trace_trans; [apply trace_eq_weakenl; apply IHn|].
      apply sub_trace_plus_cong; apply Trace_lt_sub; nliamega.
    Qed.

    Lemma PairPair_precise
    : forall n e1 e2 e3,
        trace_eq (Trace_lt (E_Pair e1 (E_Pair e2 e3)) ((n * n) * (n * n)))
                 (trace_plus (Trace_lt e1 (n * n))
                             (trace_plus (Trace_lt e2 n)
                                         (Trace_lt e3 n))).
    Proof.
      intros n e1 e2 e3.
      eapply trace_eq_trans; [apply Pair_precise|].
      apply trace_plus_cong; [apply trace_eq_refl| ].
      apply Pair_precise.
    Qed.

    Lemma Pair_Fair_precise :
      forall n, trace_eq (Trace_lt E_PairNN (n * n)) (Tracing (z_to_n n) (z_to_n n) empty_set' empty_set').
    Proof.
      induction n.
      compute; tauto.
      apply trace_eq_trans
      with (t2 := (trace_plus (Trace_lt E_PairNN (n * n))
                              (Trace_from_to E_PairNN (n * n) (S n * S n)))).
      apply trace_from_to_0_split; nliamega.
      apply trace_eq_trans with (t2 := (trace_plus (Tracing (z_to_n n) (z_to_n n) empty_set' empty_set')
                                                   (Tracing (z_to_n (S n)) (z_to_n (S n)) empty_set' empty_set'))).
      apply trace_plus_cong; auto.
      apply PairNN_layer.
      apply trace_eq_trans with (t2 := (Tracing (z_to_n (S n)) (z_to_n (S n))) empty_set' empty_set').
      unfold trace_eq.
      split4;
        [ (apply subset_union_eq; unfold z_to_n at 2; fold z_to_n; apply set_subset_add; apply subset_refl)
        | (apply subset_union_eq; unfold z_to_n at 2; fold z_to_n; apply set_subset_add; apply subset_refl)
        | apply set_eq_refl
        | apply set_eq_refl ].

      apply trace_eq_refl.
    Qed.

    Theorem Pair_Fair : Fair2 E_Pair.
      unfold Fair2.
      intros n.
      exists ((S n) * (S n)).

      fold E_PairNN.
      remember (Trace_lt E_PairNN (S n * S n)) as t.
      destruct t as [t0 t1 t2 t3].
      split; [nliamega|].
      remember (Pair_Fair_precise (S n)) as Hteq; clear HeqHteq.
      unfold trace_eq in Hteq.
      remember (Trace_lt E_PairNN (S n * S n)) as t'.
      destruct t'.
      inversion Heqt; subst s s0.
      destruct4 Hteq.
      eapply set_eq_trans; [| apply set_eq_symm]; eauto.
    Qed.
  End PairFair.

  Section NaiveTripleUnfair.

    Definition NaiveTriple3 e1 e2 e3 :=
      E_Pair e1 (E_Pair e2 e3).

    Definition traceNP3 := Trace_lt (NaiveTriple3 (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)).

    Definition NP3T := NaiveTriple3 (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat).

    Theorem NaiveTripleUnfair : ~ (Fair3 NaiveTriple3).
    Proof.

      apply AltUnfair3Suff.
      unfold AltUnfair3.
      fold NP3T.
      exists 15.
      intros n H.
      assert (16 <= n) as H' by nliamega ; clear H.
      remember (Trace_lt NP3T n) as t; destruct t as [t0 t1 t2 t3].
      destruct (sqrt_4th_root_spread n) as [m [p [[Hmn Hnp] Hppmm]]]; auto.

      left.
      assert (~ subset t0 t1); [ | intros []; contradiction].

      assert (subset (z_to_n m) t0).
      - remember (Trace_lt NP3T (m * m)) as t; destruct t as [mm0 mm1 mm2 mm3].
        assert (sub_trace (Trace_lt NP3T (m * m)) (Trace_lt NP3T n))
          by (apply Trace_lt_sub; auto).
        unfold sub_trace in H.
        rewrite <-Heqt in H.
        rewrite <-Heqt0 in H.
        destruct4 H.
        eapply subset_trans; try eassumption.
        clear H H0 H1 H2; clear dependent t0; clear t1 t2 t3.
        unfold NP3T, NaiveTriple3 in *.
        remember (Pair_precise m (E_Trace zero E_Nat) (E_Pair (E_Trace one E_Nat) (E_Trace two E_Nat))).
        clear Heqt.
        rewrite <-Heqt0 in t.
        remember ((trace_plus (Trace_lt (E_Trace zero E_Nat) m) (Trace_lt (E_Pair (E_Trace one E_Nat) (E_Trace two E_Nat)) m))).
        destruct t0.
        replace mm0 with (trace_proj zero (Tracing mm0 mm1 mm2 mm3)) by auto.
        eapply subset_trans; [| apply trace_eq_proj;  eassumption].
        rewrite Heqt1.
        rewrite trace_proj_plus_distrl.
        apply subset_union_transl.
        apply trace_lt_Nat.

      - assert (subset t1 (z_to_n p)).
        remember (Trace_lt NP3T ((p * p) * (p * p))) as p4t.
        assert (sub_trace (Trace_lt NP3T n) p4t) by (subst; apply Trace_lt_sub; auto; nliamega).
        destruct p4t as [pt0 pt1 pt2 pt3].
        unfold sub_trace in H0.
        rewrite <-Heqt in H0.
        destruct4 H0.
        eapply subset_trans; try eassumption.
        clear H0 H1 H2 H3; clear dependent t0; clear t1 t2 t3; clear dependent m; clear dependent n.
        unfold NP3T in Heqp4t.
        unfold NaiveTriple3 in Heqp4t.
        remember (PairPair_precise p (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)).
        clear Heqt.
        rewrite <-Heqp4t in t.
        apply set_subset_weaken.
        replace pt1 with (trace_proj one (Tracing pt0 pt1 pt2 pt3)) by trivial.
        clear Heqp4t.
        eapply set_eq_trans.
        apply trace_eq_proj.
        apply t.
        apply set_eq_symm.
        eapply set_eq_trans.
        apply trace_lt_Nat with (tg := one).
        rewrite trace_proj_plus_distrl.
        rewrite trace_proj_plus_distrl.
        rewrite trace_lt_Nat_off with (tg2 := zero); [| discriminate].
        rewrite trace_lt_Nat_off with (tg2 := two); [| discriminate].
        apply set_eq_symm.
        eapply set_eq_trans; [apply set_union_unitl|].
        eapply set_eq_trans; [apply set_union_unitr|].
        apply set_eq_refl.

        intros Hsub01.
        eapply z_to_n_nosub; [apply Hppmm|].
        repeat (eapply subset_trans; try eassumption); apply subset_refl.
    Qed.
  End NaiveTripleUnfair.
End Fairness.
