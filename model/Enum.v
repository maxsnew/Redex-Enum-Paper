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

Theorem Pairing_from_dec:
  forall n,
    { xy | Pairing n (fst xy) (snd xy) }.
Proof.
  intros n.
Admitted.

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

Fixpoint subset (s1 s2 : set nat) :=
  match s1 with
    | nil => True
    | x :: more =>
      set_In x s2 /\ subset more s2
  end.
Hint Unfold subset.

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
           
Example set_eq_test : (set_eq (set_add' 1 (set_add' 0 empty_set'))
                              (set_add' 0 (set_add' 1 empty_set'))).
Proof.
  compute.
  tauto.
Qed.

Definition Fair (k : Enum -> Enum -> Enum) :=
  forall n,
    exists equilibrium l_uses r_uses,
      n < equilibrium
      /\ set_eq l_uses r_uses
      /\ Trace_less_than (k (E_Trace lft E_Nat) (E_Trace rght E_Nat)) equilibrium = (l_uses, r_uses).

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

(* Proof idea: equilibrium = 2 * n + 2,  uses = 0..(S n) *)
Theorem Sum_Fair : Fair E_Sum.
Proof.
  unfold Fair.
  intros n.
  exists (2 * n + 2).
  exists (set_add' (S n) empty_set').
  split.
  omega.

  induction n; auto.

  replace (2 * S n + 2) with (S (S (2 * n + 2))) by omega.
  simpl.
  replace (n + (n + 0) + 2) with (2 * n + 2) by omega.
  rewrite IHn; clear IHn.
  replace (2 * n + 2) with (S (S (2 * n))) in * by omega.

  assert (even (S (S (2 * n)))).
  (* Goal: even (2n+2)*)
  apply double_even.
  replace (S (S (2 * n))) with (2 * (S n)) by omega.
  rewrite div2_double.
  unfold double.
  omega.

  
  replace (Trace_on (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (S (S (2 * n)))) with (trace_one 1 lft).
  replace (Trace_on (E_Sum (E_Trace lft E_Nat) (E_Trace rght E_Nat)) (S (S (S (2 * n))))) with (trace_one 1 rght).
  auto.


  (* Trace (left + right) (2n+3) = (0, 1) *)
  - remember (even_odd_dec (S (S (S (2 * n))))).
    destruct s.

    (* Contradiction: even (2n + 3)*)
    assert (odd (S (S (S (2 * n))))).
    apply odd_S; auto.
    apply False_ind; eapply not_even_and_odd; eauto.

    (* Correct: odd (2n+3) *)
    remember (Sum_Parity_Trace (S (S (S (2 * n))))).
    clear Heqe.
    rewrite <-Heqs in e.
    unfold trace_one in *.
    unfold set_add' in *.
    unfold empty_set' in *.
    simpl in e.
    auto.
    

  (* Trace (left + right) (2n+2) = (1, 0) *)
  - remember (even_odd_dec (S (S (2 * n)))) as Heo; destruct Heo as [Hev | Hod].

    (* Correct: even (2n+2)*)
    remember (Sum_Parity_Trace (S (S (2 * n)))) as Hspt; clear HeqHspt.
    rewrite <-HeqHeo in Hspt.
    auto.

    (* Contradiction: odd (2n + 2) *)
    apply False_ind.
    eapply not_even_and_odd; eauto.
Qed.

Theorem Pair_Fair : Fair E_Pair.
Admitted.

(* Cant' prove (cons e1 (cons e2 e3)) is unfair because you need to trace 3 things.. *)

Recursive Extraction Enumerates_to_dec Enumerates_from_dec.
