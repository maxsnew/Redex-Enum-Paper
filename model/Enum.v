Inductive Enum : Set :=
| E_Nat : Enum
| E_Pair : Enum -> Enum -> Enum.
Hint Constructors Enum.

Inductive Value : Set :=
| V_Nat : nat -> Value
| V_Pair : Value -> Value -> Value.
Hint Constructors Value.

Variable Pairing : nat -> nat -> nat -> Prop.
Variable Pairing_to : nat -> nat -> nat.
Variable Pairing_to_sound :
  forall l r,
    Pairing (Pairing_to l r) l r.
Hint Resolve Pairing_to_sound.
Variable Pairing_from : nat -> (nat * nat).
Variable Pairing_from_sound :
  forall n l r,
    (l, r) = Pairing_from n ->
    Pairing n l r.
Hint Resolve Pairing_from_sound.
Variable Pairing_from_fun :
  forall l r n1 n2,
    Pairing n1 l r ->
    Pairing n2 l r ->
    n1 = n2.
Variable Pairing_to_l_fun :
  forall n l1 l2 r1 r2,
    Pairing n l1 r1 ->
    Pairing n l2 r2 ->
    l1 = l2.
Variable Pairing_to_r_fun :
  forall n l1 l2 r1 r2,
    Pairing n l1 r1 ->
    Pairing n l2 r2 ->
    r1 = r2.

Inductive Enumerates : Enum -> nat -> Value -> Prop :=
| ES_Nat :
  forall n,
    Enumerates E_Nat n (V_Nat n)
| ES_Pair :
  forall l r n ln rn lx rx,
    Pairing n ln rn ->
    Enumerates l ln lx ->
    Enumerates r rn rx ->
    Enumerates (E_Pair l r) n (V_Pair lx rx).
Hint Constructors Enumerates.

Theorem Enumerates_to_fun :
  forall e x n1 n2,
    Enumerates e n1 x ->
    Enumerates e n2 x ->
    n1 = n2.
Proof.
  induction e; intros x n1 n2 E1 E2; inversion E1; inversion E2.
  
  congruence.

  subst.
  replace lx0 with lx in *; try congruence.
  replace rx0 with rx in *; try congruence.
  erewrite (IHe1 _ _ _ H2 H9) in *.
  erewrite (IHe2 _ _ _ H5 H12) in *.
  erewrite (Pairing_from_fun _ _ _ _ H1 H8) in *.
  auto.
Qed.

Theorem Enumerates_from_fun :
  forall e n x1 x2,
    Enumerates e n x1 ->
    Enumerates e n x2 ->
    x1 = x2.
Proof.
  induction e; intros x n1 n2 E1 E2; inversion E1; inversion E2; eauto.

  subst.
  erewrite (Pairing_to_l_fun _ _ _ _ _ H1 H8) in *.
  erewrite (Pairing_to_r_fun _ _ _ _ _ H1 H8) in *.
  erewrite (IHe1 _ _ _ H2 H9) in *.
  erewrite (IHe2 _ _ _ H5 H12) in *.
  auto.
Qed.

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
Qed.

Definition Enumerates_from_dec:
  forall e n,
    { x | Enumerates e n x }.
Proof.
  induction e.

  eauto.

  intros n. 
  rename e1 into l. rename e2 into r.
  remember (Pairing_from n) as PF.
  destruct PF as [ln rn].
  destruct (IHe1 ln) as [lx EL].
  destruct (IHe2 rn) as [rx ER].
  eauto.
Qed.

Extraction Enumerates_to_dec.
Extraction Enumerates_from_dec.
