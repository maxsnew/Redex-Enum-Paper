Require Import Omega.

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

Definition Trace := prod nat nat.

Definition trace_zero : Trace := (0, 0).
Definition trace_plus (t1 t2 : Trace) : Trace :=
  let (l1, r1) := t1
  in 
  let (l2, r2) := t2
  in 
  (l1 + l2, r1 + r2).

Definition trace_left n (t : Trace) : Trace :=
  let (_, r) := t
  in (n, r).

Definition trace_right n (t : Trace) : Trace :=
  let (l, _) := t
  in (l, n).

Inductive Enumerates : Enum -> nat -> Value -> Trace -> Prop :=
| ES_Trace_Left :
    forall n e v t,
      Enumerates e n v t ->
      Enumerates (E_Trace lft e) n v (trace_left 1 t)
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
    Enumerates (E_Sum l r) n (V_Sum_Right rx) t.
Hint Constructors Enumerates.

Theorem Enumerates_to_fun :
  forall e x n1 n2 t,
    Enumerates e n1 x t ->
    Enumerates e n2 x t ->
    n1 = n2.
Admitted.
(* Proof. *)
(*   induction e; intros x n1 n2 t E1 E2; inversion E1; inversion E2; subst; try congruence. *)

(*   replace lx0 with lx in *; try congruence. *)
(*   replace rx0 with rx in *; try congruence. *)
(*   replace lt0 with lt in *. *)
(*   Focus 2. *)
  
(*   assert (ln = ln0). *)
(*   - apply IHe1 with (x := lx) (t := lt). *)
(*     assumption. *)
    
(*   remember (IHe1 lx ln rn _ _). *)
(*   erewrite (IHe1 lx ln rn _ _) in *. *)
(*   erewrite (IHe2 _ _ _ H5 H12) in *. *)
(*   erewrite (Pairing_from_fun _ _ _ _ H1 H8) in *. *)
(*   auto. *)

(*   subst. *)
(*   erewrite (Bijects_fun_right _ _ _ _ _ _ H1 H7) in *. *)
(*   erewrite (IHe _ _ _ H4 H10) in *. *)
(*   auto. *)

(*   subst. *)
(*   inversion H12. subst lx0 rx0. *)
(*   erewrite (IHe _ _ _ H3 H10) in *. *)
(*   erewrite (H _ _ _ _ H6 H13) in *. *)
(*   erewrite (Pairing_from_fun _ _ _ _ H2 H9) in *. *)
(*   auto. *)

(*   subst. *)
(*   inversion H9. subst lx0. *)
(*   erewrite (IHe1 _ _ _ H4 H10). *)
(*   auto. *)

(*   subst. *)
(*   congruence. *)

(*   subst. *)
(*   congruence. *)

(*   subst. *)
(*   inversion H9. subst rx0. *)
(*   erewrite (IHe2 _ _ _ H4 H10). *)
(*   auto. *)
(* Qed. *)

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
  induction e; intros x n1 n2 t1 t2 E1 E2; inversion E1; inversion E2; eauto; subst.
  
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

Lemma Enumerates_to_dec_Map :
  forall b e x,
    (forall x,
      { n | Enumerates e n x }
      + { forall n, ~ Enumerates e n x }) ->
    { n | Enumerates (E_Map b e) n x }
    + { forall n, ~ Enumerates (E_Map b e) n x }.
Proof.
  intros b e x IHe.
  destruct (Bijects_to_dec _ _ b x) as [y B].
  destruct (IHe y) as [[n IHE] | NIH].
  
  left. exists n. eauto.
  right. intros n E.
  inversion E. subst n0 x0 inner bi.
  rename H1 into B'. rename H4 into IHE.
  erewrite (Bijects_fun_right _ _ _ _ _ _ B B') in *.
  eapply NIH. apply IHE.
Defined.
Hint Resolve Enumerates_to_dec_Map.

Definition Enumerates_to_dec:
  forall e x,
    { n | Enumerates e n x } + { forall n, ~ Enumerates e n x }.
Proof.
  induction e; destruct x; eauto;
    try ( right; intros _n E; inversion E; fail ).

  rename x1 into lx. rename x2 into rx.
  rename e1 into l. rename e2 into r.
  destruct (IHe1 lx) as [[ln EL] | LF].
  destruct (IHe2 rx) as [[rn ER] | RF].

  left. eauto.

  right. intros _n E; inversion E.
  eapply RF. apply H6.

  right. intros _n E; inversion E.
  eapply LF. apply H5.

  destruct (IHe x1) as [[ln EL] | LF].
  destruct (H x1 x2) as [[rn ER] | RF].
  left. eauto.

  right. intros _n E; inversion E.
  eapply RF. apply H7.

  right. intros _n E; inversion E.
  eapply LF. apply H6.

  destruct (IHe1 x) as [[ln EL] | LF].
  eauto.
  right. intros _n E. inversion E.
  eapply LF. apply H4.

  destruct (IHe2 x) as [[rn ER] | RF].
  eauto.
  right. intros _n E. inversion E.
  eapply RF. apply H4.
Defined.

Lemma even_odd_eq_dec:
  forall n,
    { l | n = 2 * l } + { r | n = 2 * r + 1 }.
Proof.
 induction n as [|n]; eauto.
 destruct IHn as [[en EQ]|[on EQ]]; subst.
 right. exists en. omega.
 left. exists (S on). omega.
Defined.

Definition Enumerates_from_dec:
  forall e n,
    { x | Enumerates e n x }.
Proof.
  induction e; eauto.

  intros n.
  rename e1 into l. rename e2 into r.
  remember (Pairing_from n) as PF.
  destruct PF as [ln rn].
  destruct (IHe1 ln) as [lx EL].
  destruct (IHe2 rn) as [rx ER].
  eauto.

  intros n.
  destruct (IHe n) as [x IHE].
  destruct (Bijects_from_dec _ _ b x) as [y B].
  exists y. eauto.

  intros n.
  rename e into l. rename e0 into f.
  remember (Pairing_from n) as PF.
  destruct PF as [ln rn].
  destruct (IHe ln) as [lx EL].
  destruct (H lx rn) as [rx ER].
  exists (V_Pair lx rx). eauto.

  intros n.
  destruct (even_odd_eq_dec n) as [[ln EQ] | [rn EQ]].
  destruct (IHe1 ln) as [lx EL].
  eauto.
  destruct (IHe2 rn) as [rx ER].
  eauto.
Defined.

Recursive Extraction Enumerates_to_dec Enumerates_from_dec.
