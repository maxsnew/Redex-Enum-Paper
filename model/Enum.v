Require Import Omega.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Div2 Coq.Arith.Even.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.

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

Inductive l_or_r : Set :=
| lft : l_or_r
| rght : l_or_r.

Inductive Enum : Set :=
| E_Nat : Enum
| E_Pair : Enum -> Enum -> Enum
| E_Map : Bijection Value Value -> Enum -> Enum
| E_Dep : Enum -> (Value -> Enum) -> Enum
| E_Sum : Enum -> Enum -> Enum
| E_Trace : l_or_r -> Enum -> Enum (* A no-op wrapper to signal tracing *)
.
Hint Constructors Enum.

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

Theorem Pairing_from_fun :
  forall l r n1 n2,
    Pairing n1 l r ->
    Pairing n2 l r ->
    n1 = n2.
Proof.
  intros l r n1 n2 P1 P2.
  inversion P1; inversion P2; subst; omega.
Qed.

Require Import Psatz.
Lemma Pairing_to_incompat:
  forall l1 l2 r1 r2,
    r1 <= l1 ->
    l2 < r2 ->
    l2 + r2 * r2 = l1 * l1 + l1 + r1 ->
    False.
Proof.
Admitted.

Theorem Pairing_to_fun :
  forall n l1 l2 r1 r2,
    Pairing n l1 r1 ->
    Pairing n l2 r2 ->
    (l1 = l2) /\ (r1 = r2).
Proof.
  intros n l1 l2 r1 r2 P1 P2.
  inversion P1; inversion P2; clear P1; clear P2; subst.

  replace l1 with l2 in *. replace r1 with r2 in *. auto.
  nia. nia.

  cut False. contradiction.
  eapply (Pairing_to_incompat _ _ _ _ H H3 H4).

  cut False. contradiction.
  symmetry in H4.
  eapply (Pairing_to_incompat _ _ _ _ H3 H H4).

  replace r1 with r2 in *. replace l1 with l2 in *. auto.
  nia. nia.
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

Lemma sqrt_lemma z : (z - (sqrt z * sqrt z)) - sqrt z <= sqrt z.
Proof.
  induction z as [| z]; auto.
  (* sqrt_spec: forall n : nat, sqrt n * sqrt n <= n < S (sqrt n) * S (sqrt n) *)
  (* Nat.sqrt_succ_le: forall a : nat, sqrt (S a) <= S (sqrt a) *)
  (* Nat.sqrt_succ_or: forall a : nat, sqrt (S a) = S (sqrt a) \/ sqrt (S a) = sqrt a *)
  destruct (Nat.sqrt_succ_or z); [nia|].
  inversion IHz; [| nia].
  clear IHz.
  apply False_ind.
  rewrite <-H in H1.

  assert (z - sqrt (S z) * sqrt (S z) - sqrt (S z) = 0).
  assert (z <= sqrt (S z) * sqrt (S z) + sqrt (S z)).
  destruct (sqrt_spec z).
  admit.
  nia.
  rewrite H0 in H1.
  (* sqrt z <= z - sqrt z * sqrt z *)
  
  admit.
Qed.

Lemma sqrt_lemma' z :
  (z - (sqrt z) * (sqrt z) < (sqrt z))
  -> z = z - (sqrt z * sqrt z) + (sqrt z * sqrt z).
Proof.
  remember (sqrt_spec z); omega.
Qed.

Lemma sqrt_lemma'' k n :
  (n * n <= k < S n * S n) -> k - sqrt k * sqrt k - sqrt k < S n.
Proof.
  intros H; rewrite (Nat.sqrt_unique k n); lia.
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
  assert (z = rootz * rootz + rootz + ((z - rootz * rootz) - rootz)).
  assert (((z - (rootz * rootz)) - rootz) = z - (rootz * rootz + rootz)).
  lia.
  nia.
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

(* Eval compute in (Pairing_from_dec 0). *)
(* Eval compute in (Pairing_from_dec 1). *)
(* Eval compute in (Pairing_from_dec 2). *)
(* Eval compute in (Pairing_from_dec 3). *)
(* Eval compute in (Pairing_from_dec 4). *)
(* Eval compute in (Pairing_from_dec 5). *)
(* Eval compute in (Pairing_from_dec 6). *)
(* Eval compute in (Pairing_from_dec 7). *)
(* Eval compute in (Pairing_from_dec 8). *)
(* Eval compute in (Pairing_from_dec 9). *)
(* Eval compute in (Pairing_from_dec 10). *)
(* Eval compute in (Pairing_from_dec 11). *)

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

Definition Trace := (prod (set nat) (set nat)).

Definition empty_set' := @empty_set nat.
Definition set_union' := @set_union nat eq_nat_dec.
Definition set_add' := @set_add nat eq_nat_dec.

Definition trace_zero : Trace := (empty_set', empty_set').
Definition trace_plus (t1 t2 : Trace) : Trace :=
  let (l1, r1) := t1
  in
  let (l2, r2) := t2
  in
  (set_union' l1 l2, set_union' r1 r2).

Definition trace_one n lor : Trace :=
  match lor with
    | lft  => (set_add' n empty_set', empty_set')
    | rght => (empty_set', set_add' n empty_set')
  end.

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
    forall n lor e v _t,
      Enumerates e n v _t ->
      Enumerates (E_Trace lor e) n v (trace_one n lor)
.
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
  induction x as [|x]; intros; omega.
Qed.

Lemma odd_neq_even:
  forall x y,
    2 * x = 2 * y + 1 ->
    False.
Proof.
  induction x as [|x]; intros; omega.
Qed.

Lemma odd_fun:
  forall x y,
    2 * x + 1 = 2 * y + 1 ->
    x = y.
Proof.
  induction x as [|x]; intros; omega.
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
  forall lor e x,
    (forall x,
      { nt: nat * Trace | let (n, t) := nt in Enumerates e n x t }
      + { forall n t, ~ Enumerates e n x t }) ->
    { nt : nat * Trace | let (n, t) := nt in Enumerates (E_Trace lor e) n x t }
    + { forall n t, ~ Enumerates (E_Trace lor e) n x t }.
Proof.
  intros lor e x IHe.
  destruct (IHe x) as [[[n t] IHE] | NIH].

  left.
  exists (n, trace_one n lor); eauto.

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
  omega.
Defined.

Lemma odd_SS :
  forall n,
    { r | n = 2 * r + 1 } -> { m | S (S n) = 2 * m + 1 }.
Proof.
  intros n P.
  destruct P.
  exists ((S x)).
  omega.
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
    replace (S (2 * div2 n)) with (2 * div2 n + 1) in Hodd by omega.
    eauto.

  (* E_Trace *)
  - rename l into lor.
    destruct (IHe n) as [[x _t] E].
    exists (x, trace_one n lor).
    eauto.
Defined.

Definition Trace_on (e : Enum) (n : nat) : Trace :=
  let (nt, _) := (Enumerates_from_dec e n) in snd nt.

Fixpoint Trace_less_than (e : Enum) n : Trace :=
  match n with
    | 0 => trace_zero
    | S n' => trace_plus (Trace_on e n') (Trace_less_than e n')
  end.

Fixpoint Trace_from_to e lo hi : Trace :=
  if le_lt_dec hi lo
  then trace_zero
  else match hi with
         | 0 => trace_zero
         | S hi' => trace_plus (Trace_on e hi') (Trace_from_to e lo hi')
       end.

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
  destruct (set_In_dec eq_nat_dec a s2).

  destruct (IHs1 s2).
  left; constructor; auto.

  right.
  unfold subset; fold subset.
  intros H; destruct H; contradiction.

  right.
  intros H; destruct H; contradiction.
Defined.

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

Lemma set_subset_weaken : forall s1 s2, set_eq s1 s2 -> subset s1 s2.
Proof.
  unfold set_eq.
  tauto.
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
  unfold set_add', set_add.
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
  apply subset_refl.
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
  
  unfold set_union', set_union in *.
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
  unfold set_union', set_union.
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

Definition Fair (k : Enum -> Enum -> Enum) :=
  forall n,
  exists equilibrium,
    let (l_uses, r_uses) := Trace_less_than (k (E_Trace lft E_Nat) (E_Trace rght E_Nat)) equilibrium
    in n < equilibrium
       /\ set_eq l_uses r_uses.

Lemma Sum_Parity_Trace :
  forall n,
    Trace_on (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) n
    = trace_one (div2 n)
                (if even_odd_dec n
                 then lft
                 else rght).
Proof.
  intros n.
  remember (even_odd_dec n) as mH.
  unfold Trace_on; simpl.
  destruct mH; rewrite <-HeqmH; auto.
Qed.

Fixpoint z_to_n n : set nat :=
  match n with
    | 0 => empty_set'
    | S n' => set_add' n' (z_to_n n')
  end.

Definition n_to_z n : set nat := rev (z_to_n n).

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

Definition trace_eq (t1 t2 : Trace) : Prop :=
  let (tl1, tr1) := t1
  in
  let (tl2, tr2) := t2
  in
  set_eq tl1 tl2 /\ set_eq tr1 tr2.

Theorem trace_plus_cong t1 t2 t3 t4 : trace_eq t1 t3 -> trace_eq t2 t4 -> trace_eq (trace_plus t1 t2) (trace_plus t3 t4).
  unfold trace_eq.
  destruct t1; destruct t2; destruct t3; destruct t4.
  unfold trace_plus.
  intros H; destruct H.
  intros H'; destruct H'.
  split; apply set_union_cong; auto.
Qed.

Theorem trace_eq_refl t : trace_eq t t.
Proof.
  unfold trace_eq; destruct t; split; apply set_eq_refl.
Qed.

Theorem trace_eq_symm t1 t2 : trace_eq t1 t2 -> trace_eq t2 t1.
Proof.
  unfold trace_eq.
  destruct t1; destruct t2.
  intros H; destruct H.
  split; apply set_eq_symm; auto.
Qed.

Theorem trace_eq_trans t1 t2 t3 : trace_eq t1 t2 -> trace_eq t2 t3 -> trace_eq t1 t3.
Proof.
  unfold trace_eq.
  destruct t1; destruct t2; destruct t3.
  intros H; destruct H.
  intros H'; destruct H'.
  split; eapply set_eq_trans; eauto.
Qed.

Theorem trace_plus_comm t1 t2 : trace_eq (trace_plus t1 t2) (trace_plus t2 t1).
Proof.
  destruct t1, t2.
  unfold trace_plus.
  split; apply set_eq_union_comm.
Qed.

Theorem trace_plus_assoc t1 t2 t3 : trace_eq (trace_plus t1 (trace_plus t2 t3))
                                             (trace_plus (trace_plus t1 t2) t3).
Proof.
  destruct t1, t2, t3.
  unfold trace_plus.
  split; apply set_eq_symm; apply set_union_assoc.
Qed.

Theorem trace_lt_from_to_0_same e n : trace_eq (Trace_less_than e n) (Trace_from_to e 0 n).
Proof.
  induction n.
  simpl.
  split; apply set_eq_refl.

  simpl.
  unfold trace_plus.
  destruct (Trace_on e n).
  destruct (Trace_less_than e n).
  destruct (Trace_from_to e 0 n).
  destruct IHn.
  split.
  apply set_union_cong; [apply set_eq_refl|]; auto.
  apply set_union_cong; [apply set_eq_refl|]; auto.
Qed.

Theorem trace_plus_unitl t :
  trace_eq (trace_plus trace_zero t) t.
Proof.
  destruct t; split; apply set_union_unitl.
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

Theorem trace_from_to_self e m
: Trace_from_to e m m = trace_zero.
Proof.
  destruct m; auto.
  unfold Trace_from_to.
  remember (le_lt_dec (S m) (S m)) as l.
  destruct l; auto.
  clear Heql.
  apply lt_irrefl in l.
  contradiction.
Qed.

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
  replace (S (m + 0)) with (S m) by lia.
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
  assert (m < (S (m + S n))).
  lia.
  clear Heqt.
  apply (le_not_gt) in l.
  contradiction.
  fold Trace_from_to.
  clear l Heqt.
  remember (le_lt_dec (S (m + S n)) (S m)).
  destruct s.
  assert ((S (m + S n)) > S m) by lia.
  clear Heqs; apply le_not_gt in l; contradiction.
  replace (m + S n) with (S (m + n)) by lia.
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
  assert (n = (S (m + t))).
  lia.
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
    [apply IHn; lia| ].
  apply trace_eq_trans with (t2 := (trace_plus (Trace_from_to e m n)
                                               (trace_plus (Trace_on e n)
                                                           (Trace_from_to e (S n) p)))).
  apply trace_plus_cong; [apply trace_eq_refl| ].
  apply trace_from_to_split1l; lia.

  eapply trace_eq_trans.
  apply trace_plus_assoc.
  apply trace_plus_cong; [| apply trace_eq_refl].
  apply trace_eq_symm.
  apply trace_from_to_split1r; lia.
Qed.

Theorem trace_from_to_0_split :
  forall m n e,
    m < n ->
    trace_eq (Trace_less_than e n)
             (trace_plus (Trace_less_than e m)
                         (Trace_from_to e m n)).
Proof.
  intros m n e Hmn.
  eapply trace_eq_trans.
  apply trace_lt_from_to_0_same.
  eapply trace_eq_trans.
  apply trace_from_to_split with (n := m); split; [lia | assumption].
  apply trace_plus_cong.
  apply trace_eq_symm.
  apply trace_lt_from_to_0_same.
  apply trace_eq_refl.
Qed.

Eval compute in (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 20).
Eval compute in (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 21).
Eval compute in (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 22).
Eval compute in (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 23).
Eval compute in (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 24).
Eval compute in (z_to_n 10).
Eval compute in (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 20).


(* Proof idea: equilibrium = 2 * n + 2,  uses = 0..(S n) *)
Theorem Sum_Fair : Fair E_Sum.
Proof.
  unfold Fair.
  intros n.
  exists (2 * n + 2).
  remember (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (2 * n + 2)).
  destruct t as [tl tr].
  split.
  omega.

  generalize dependent tr.
  generalize dependent tl.
  induction n.
  intros tr tl Heqt.
  inversion Heqt; auto; apply set_eq_refl.

  intros tl tr Htltr.
  remember (Trace_less_than (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (2 * n + 2)).
  replace (2 * S n + 2) with (S (S (2 * n + 2))) in Htltr by omega.
  simpl in Htltr.
  replace (n + (n + 0) + 2) with (2 * n + 2) in Htltr by omega.
  destruct t as [tl' tr'].
  assert (set_eq tl' tr').
  apply IHn; auto.
  rewrite <-Heqt in Htltr.
  clear Heqt.
  clear IHn.
  replace (Trace_on (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (S (2 * n + 2))) with (trace_one (S n) rght) in Htltr.
  
  replace (Trace_on (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) ((2 * n)+2)) with (trace_one (S n) lft) in Htltr.
  unfold trace_one in Htltr.
  unfold trace_plus in Htltr.
  inversion Htltr.
  clear tl tr Htltr H1 H2.

  - SearchAbout set_eq.
    apply set_eq_trans with (s2 := set_union' (S n :: nil) tl').
    apply set_union_unitl.
    apply set_eq_trans with (s2 := set_union' (S n :: nil) tr').
    apply set_union_cong; auto.
    apply set_eq_refl.
    apply set_union_cong.
    apply set_eq_refl.
    apply set_eq_symm.
    apply set_union_unitl.

  (* Trace (left + right) (2n+3) =  *)
  - unfold Trace_on.
    destruct (Enumerates_from_dec (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (2 * n + 2)).
    assert (Enumerates (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (2 * n + 2) (V_Sum_Left (V_Nat (S n))) (trace_one (S n) lft)).
    apply ES_Sum_Left with (ln := (S n)).
    omega.
    econstructor.
    constructor.
    destruct x.
    
    destruct (Enumerates_from_fun _ _ _ _ _ _ y H0); subst.
    auto.

  - unfold Trace_on.
    destruct (Enumerates_from_dec (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (S (2 * n + 2))).
    assert (Enumerates (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (S (2 * n + 2)) (V_Sum_Right (V_Nat (S n))) (trace_one (S n) rght)).
    apply ES_Sum_Right with (rn := S n).
    omega.
    econstructor; constructor.
    destruct x.
    destruct (Enumerates_from_fun _ _ _ _ _ _ y H0); subst.
    auto.
Qed.

Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 0).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 1).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 4).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 9).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 16).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 25).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 36).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 49).
Eval compute in (Trace_less_than (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)) 64).

Definition E_PairNN := (E_Pair (E_Trace lft E_Nat) (E_Trace rght E_Nat)).

Eval compute in z_to_n 0.

Theorem z_to_n_correct n x
: In x (z_to_n n) <-> x < n.
Proof.
  generalize dependent x.
  induction n.
  
  intros x; compute; split; [apply False_ind | intros contra; inversion contra].
  intros x.
  destruct (eq_nat_dec x n).
  simpl.
  subst.
  split; [lia|].
  intros _.
  apply set_add_intro2; auto.
  
  split.
  simpl.
  intros H.
  assert (In x (z_to_n n)).
  apply set_add_elim2 with (b := n) (Aeq_dec := eq_nat_dec); auto.
  assert (x < n).
  apply IHn.
  auto.
  lia.

  intros H.
  simpl.
  apply set_add_intro1.
  apply IHn.
  lia.
Qed.

Theorem In_trace' (lor : l_or_r) e x m n :
  set_In x ((if lor then @fst (set nat) (set nat) else (@snd (set nat) (set nat))) (Trace_from_to e m (S (m + n))))
  <->
  (exists k,
     m <= k < S (m + n) /\ set_In x ((if lor then @fst (set nat) (set nat) else (@snd (set nat) (set nat))) (Trace_on e k))).
Proof.
  split.
  generalize dependent m.
  induction n; intros m;
    [
      replace (S (m + 0)) with (S m) by lia;
      destruct lor;
      (intros H; exists m; split; [lia |];
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
      destruct (le_lt_dec (S (m + S n)) m) as [contra | _]; [ assert (~ (S (m + S n)) <= m) by (apply gt_not_le; lia); contradiction|];
      unfold trace_plus;
      remember (Trace_on e (m + S n))as t; destruct t as [tl tr];
      remember (Trace_from_to e m (m + S n)) as t; destruct t as [tl' tr'];
      replace (m + S n) with (S (m + n)) in * by lia;
      destruct lor;
      (simpl; intros Hin_union; unfold set_union' in Hin_union;
       destruct (set_union_elim eq_nat_dec _ _ _ Hin_union); 
       [exists (S (m + n)); split; [lia|]; destruct Heqt; auto |]);
      [ replace tl' with (fst (Trace_from_to e m (S (m + n)))) in H by (rewrite <-Heqt0; auto)
      | replace tr' with (snd (Trace_from_to e m (S (m + n)))) in H by (rewrite <-Heqt0; auto)];
      (destruct (IHn m H) as [k [Hless Hinn]]; exists k; (split; [lia | auto]))].

  intros [k [[Hmk HkSmn] Hin]];
  induction n as [| n].
  replace (S (m + 0)) with (S m) in * by lia;
  unfold Trace_from_to;
  destruct (le_lt_dec (S m) m); [apply le_Sn_n in l; contradiction|];
  fold Trace_from_to; rewrite trace_from_to_self; assert (k = m) by lia; subst;
  destruct lor;
  remember (trace_plus (Trace_on e m) trace_zero) as t;
  destruct t; simpl in *;
  remember (Trace_on e m) as t';
    destruct t';
    simpl in *;
  inversion Heqt; subst; auto.

  replace (S (m + n)) with (m + S n) in * by lia;
  destruct (eq_nat_dec k (m + S n)); subst;
  unfold Trace_from_to; fold Trace_from_to;
  (destruct (le_lt_dec (S (m + S n)) m); [ assert (~ (S (m + S n) <= m)) by (apply le_not_gt; lia); contradiction| ]); (remember (Trace_on e (m + S n)) as t); destruct t as [tl tr];
   (remember (Trace_from_to e m (m + S n)) as t'); destruct t' as [tl' tr'].
  destruct lor; (
      simpl in *; unfold set_union'; apply set_union_intro1; auto).

  destruct lor; simpl in *; unfold set_union'; apply set_union_intro2; apply IHn; lia.
Qed.

Theorem In_Trace (lor : l_or_r) e x m n :
  (m < n) ->
  (In x ((if lor then @fst (set nat) (set nat) else (@snd (set nat) (set nat))) (Trace_from_to e m n)) <->
   (exists k,
     m <= k < n /\ In x ((if lor then @fst (set nat) (set nat) else (@snd (set nat) (set nat))) (Trace_on e k)))).
Proof.
  intros H.
  remember (pred (n - m)) as p.
  assert (n = (S (m + p))) by lia.
  subst n.
  apply In_trace'.
Qed.

Eval compute in Trace_less_than E_PairNN (S (5 * 5)).

Lemma PairNN_layer :
  forall n,
    trace_eq (Trace_from_to E_PairNN (n * n) (S n * S n))
             (z_to_n (S n), z_to_n (S n)).
Proof.
  intros n;
    unfold trace_eq;
    remember (Trace_from_to E_PairNN (n * n) (S n * S n)) as t;
    destruct t as [tl tr];
    split; split.

  (* Case 1: trace_left pair n^2 (n+1)^2 < 0..n+1 *)
  apply subset_In_def;
    assert (tl = (fst (Trace_from_to E_PairNN (n * n) (S n * S n)))) by (rewrite <-Heqt; auto);
    intros x Hin;
    apply z_to_n_correct;
    rewrite H in Hin;
    (apply (In_Trace lft) in Hin; [| lia]);
    destruct Hin as [k [Hksize Hin]];
    clear Heqt H;
    unfold Trace_on in Hin;
    destruct (Enumerates_from_dec E_PairNN k) as [[v t] Henum];
    destruct (le_lt_dec (sqrt k) (k - (sqrt k * sqrt k))).
  assert (Enumerates E_PairNN
                     k
                     (V_Pair (V_Nat (sqrt k)) (V_Nat ((k - sqrt k * sqrt k) - sqrt k)))
                     (trace_plus (trace_one (sqrt k)                         lft)
                                 (trace_one ((k - sqrt k * sqrt k) - sqrt k) rght)
                     )).
  
  apply ES_Pair with (ln := (sqrt k)) (rn := ((k - sqrt k * sqrt k) - sqrt k));
    [| econstructor; constructor
     | econstructor; constructor
    ];
    assert (k = (sqrt k * sqrt k) + sqrt k + ((k - sqrt k * sqrt k) - sqrt k)) as Hk by nia;
    rewrite Hk at 1;
    constructor;
    apply sqrt_lemma.
  destruct (Enumerates_from_fun _ _ _ _ _ _ Henum H); subst;
    destruct Hin; [nia | contradiction].

  assert (Enumerates E_PairNN
                     k
                     (V_Pair (V_Nat (k - (sqrt k * sqrt k)))
                             (V_Nat (sqrt k)))
                     (trace_plus (trace_one (k - (sqrt k * sqrt k)) lft)
                                 (trace_one (sqrt k)                rght))).
  apply ES_Pair with (ln := (k - (sqrt k * sqrt k))) (rn := sqrt k);
    [ rewrite (sqrt_lemma' k) at 1; [constructor; auto | auto]
    | econstructor; constructor
    | econstructor; constructor ].
  destruct (Enumerates_from_fun _ _ _ _ _ _ Henum H); subst;
    destruct Hin; [nia | contradiction].

  (* Case 2: 0..n+1 < trace_left pair n^2 (n+1)^2 *)
  apply subset_In_def;
    intros x Hin;
    apply z_to_n_correct in Hin;
    assert (tl = (fst (Trace_from_to E_PairNN (n * n) (S n * S n)))) by (rewrite <-Heqt; auto);
    rewrite H;
    (apply (In_Trace lft); [lia| ]);
  (* our k is (unpair x n)
   *)
    destruct (le_lt_dec n x).
  
  exists (x*x + x + n); split; [nia|];
    unfold Trace_on;
    destruct (Enumerates_from_dec E_PairNN (x * x + x + n)) as [[v t] Henum];
    assert (Enumerates E_PairNN
                     (x * x + x + n)
                     (V_Pair (V_Nat x) (V_Nat n))
                     (trace_plus (trace_one x lft) (trace_one n rght))).
  econstructor;
    [ constructor 1; auto
    | econstructor; constructor
    | econstructor; constructor
    ].
  destruct (Enumerates_from_fun _ _ _ _ _ _ Henum H0); subst; simpl; tauto.

  exists (x + n * n); split; [lia|];
    unfold Trace_on;
    destruct (Enumerates_from_dec E_PairNN (x + n * n)) as [[v t] Henum];
    assert (Enumerates E_PairNN
                       (x + n * n)
                       (V_Pair (V_Nat x) (V_Nat n))
                       (trace_plus (trace_one x lft) (trace_one n rght))).
  econstructor;
    [ constructor 2; auto
    | econstructor; constructor
    | econstructor; constructor ].
  destruct (Enumerates_from_fun _ _ _ _ _ _ Henum H0); subst; simpl; tauto.

  (* this half of the proof is almost exactly the same as above,
     except with tr instead of tl should figure how to be less
     repetitive than repeating all the above tactics.  might be less
     of a problem when we move to a new trace representation
   *)
  (* Case 3: trace_right pair n^2 (n+1)^2 < 0..n+1 *)
  apply subset_In_def;
    assert (tr = (snd (Trace_from_to E_PairNN (n * n) (S n * S n)))) by (rewrite <-Heqt; auto);
    intros x Hin;
    apply z_to_n_correct;
    rewrite H in Hin;
    (apply (In_Trace rght) in Hin; [| lia]);
    destruct Hin as [k [Hksize Hin]];
    clear Heqt H;
    unfold Trace_on in Hin;
    destruct (Enumerates_from_dec E_PairNN k) as [[v t] Henum].
    destruct (le_lt_dec (sqrt k) (k - (sqrt k * sqrt k))).
  assert (Enumerates E_PairNN
                     k
                     (V_Pair (V_Nat (sqrt k)) (V_Nat ((k - sqrt k * sqrt k) - sqrt k)))
                     (trace_plus (trace_one (sqrt k)                         lft)
                                 (trace_one ((k - sqrt k * sqrt k) - sqrt k) rght)
                     )).
  
  apply ES_Pair with (ln := (sqrt k)) (rn := ((k - sqrt k * sqrt k) - sqrt k));
    [| econstructor; constructor
     | econstructor; constructor
    ];
    assert (k = (sqrt k * sqrt k) + sqrt k + ((k - sqrt k * sqrt k) - sqrt k)) as Hk by nia;
    rewrite Hk at 1;
    constructor;
    apply sqrt_lemma.
  destruct (Enumerates_from_fun _ _ _ _ _ _ Henum H); subst;
    destruct Hin;
    [ rewrite <- H0; apply sqrt_lemma''; auto
    | contradiction].

  assert (Enumerates E_PairNN
                     k
                     (V_Pair (V_Nat (k - (sqrt k * sqrt k)))
                             (V_Nat (sqrt k)))
                     (trace_plus (trace_one (k - (sqrt k * sqrt k)) lft)
                                 (trace_one (sqrt k)                rght))).
  apply ES_Pair with (ln := (k - (sqrt k * sqrt k))) (rn := sqrt k);
    [ rewrite (sqrt_lemma' k) at 1; [constructor; auto | auto]
    | econstructor; constructor
    | econstructor; constructor ].
  destruct (Enumerates_from_fun _ _ _ _ _ _ Henum H); subst;
  destruct Hin;
  [ rewrite <-H0; rewrite (Nat.sqrt_unique k n); lia
  | contradiction
  ].
  
    
Qed.

(* TODO: cleanup. Why do I need to use PairNN_layer 3 times? *)
Lemma Pair_Fair_precise :
  forall n, trace_eq (Trace_less_than E_PairNN (n * n)) (z_to_n n, z_to_n n).
Proof.
  induction n.
  compute; tauto.
  apply trace_eq_trans
  with (t2 := (trace_plus (Trace_less_than E_PairNN (n * n))
                          (Trace_from_to E_PairNN (n * n) (S n * S n)))).
  apply trace_from_to_0_split; lia.
  apply trace_eq_trans with (t2 := (Trace_from_to E_PairNN (n * n) (S n * S n))).
  apply trace_eq_trans with (t2 := (trace_plus (z_to_n n, z_to_n n) (z_to_n (S n), z_to_n (S n)))).
  apply trace_plus_cong.
  auto.
  apply PairNN_layer.
  apply trace_eq_trans with (t2 := (z_to_n (S n), z_to_n (S n))).
  split; (apply subset_union_eq; unfold z_to_n at 2; fold z_to_n; apply set_subset_add; apply subset_refl).
  apply trace_eq_symm.
  apply PairNN_layer.
  apply PairNN_layer.
Qed.
  
Theorem Pair_Fair : Fair E_Pair.
  unfold Fair.
  intros n.
  exists ((S n) * (S n)).
  
  fold E_PairNN.
  remember (Trace_less_than E_PairNN (S n * S n)) as t.
  destruct t as [tl tr].
  split.
  nia.
  remember (Pair_Fair_precise (S n)) as Hteq; clear HeqHteq.
  unfold trace_eq in Hteq.
  remember (Trace_less_than E_PairNN (S n * S n)) as t'.
  destruct t'.
  inversion Heqt; subst s s0.
  destruct Hteq.
  eapply set_eq_trans; eauto.
  apply set_eq_symm; auto.
Qed.

(* Cant' prove (cons e1 (cons e2 e3)) is unfair because you need to trace 3 things.. *)

Recursive Extraction Enumerates_to_dec Enumerates_from_dec.
