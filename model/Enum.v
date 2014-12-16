
(* XXX I tried to make this Set -> Set and have Enum track what it
returns, but it had to be Set -> Type. I thought this was what was
complicating the _fun proofs, but it wasn't *)

Inductive Enum : Set :=
| E_Nat : Enum
| E_Pair : Enum -> Enum -> Enum.
Hint Constructors Enum.

Fixpoint Enum_Type e :=
  match e with
    | E_Nat => nat
    | E_Pair l r =>
      (prod (Enum_Type l) (Enum_Type r))
  end.

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

Inductive Enumerates : forall (e:Enum), nat -> (Enum_Type e) -> Prop :=
| ES_Nat :
  forall n,
    Enumerates E_Nat n n
| ES_Pair :
  forall l r n ln rn lx rx,
    Pairing n ln rn ->
    Enumerates l ln lx ->
    Enumerates r rn rx ->
    Enumerates (E_Pair l r) n (lx,rx).
Hint Constructors Enumerates.

Theorem Enumerates_to_fun :
  forall e x n1 n2,
    Enumerates e n1 x ->
    Enumerates e n2 x ->
    n1 = n2.
Proof.
  induction e; intros x n1 n2 E1 E2.
Admitted.

Theorem Enumerates_from_fun :
  forall e n x1 x2,
    Enumerates e n x1 ->
    Enumerates e n x2 ->
    x1 = x2.
Proof.
  induction e; intros n x1 x2 E1 E2.
Admitted.

Definition Enumerates_to_dec:
  forall e x,
    { n | Enumerates e n x }.
Proof.
  induction e.

  eauto.

  intros [lx rx]. 
  rename e1 into l. rename e2 into r.  
  destruct (IHe1 lx) as [ln EL].
  destruct (IHe2 rx) as [rn ER].
  eauto.
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
  simpl.
  eauto.
Qed.

Extraction Enumerates_to_dec.
Extraction Enumerates_from_dec.
