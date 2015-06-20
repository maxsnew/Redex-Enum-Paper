Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Arith_base Coq.Arith.Even Coq.Arith.Div2.
Require Import Psatz.
Require Import Enum.Util Enum.EvenOddPow.
Require Import Coq.Program.Wf Init.Wf.
Require Coq.Program.Wf.
Include WfExtensionality.


Inductive Unfair_Pairing : nat -> nat -> nat -> Prop :=
| UnfairPair :
    forall x y,
      Unfair_Pairing ((pow 2 y) * (2 * x + 1) - 1) x y.
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

Lemma unfair_unique :
  forall x1 x2 y1 y2,
    2 ^ y2 * (2 * x2 + 1) - 1 = 2 ^ y1 * (2 * x1 + 1) - 1
    -> x1 = x2 /\ y1 = y2.
Proof.
  intros x1 x2 y1 y2 MINUS.
  assert (2 ^ y2 * (2 * x2 + 1) = 2 ^ y1 * (2 * x1 + 1)) as NO_MINUS.
  remember (2 ^ y2 * (2 * x2 + 1)) as a2.
  remember (2 ^ y1 * (2 * x1 + 1)) as a1.
  destruct a2 as [|a2'].
  apply pow_S_prod_false in Heqa2; intuition.
  destruct a1 as [|a1'].
  apply pow_S_prod_false in Heqa1; intuition.
  nliamega.
  clear MINUS.
  generalize NO_MINUS; clear NO_MINUS.

  generalize y1; clear y1.
  induction y2; intros y1 FACT.
  replace (2^0) with 1 in FACT;[|unfold pow;nliamega].
  rewrite mult_1_l in FACT.
  destruct y1.
  split;auto.
  replace (2^0) with 1 in FACT;[|unfold pow;nliamega].
  nliamega.
  unfold pow in FACT; fold pow in FACT.
  symmetry in FACT.
  rewrite <- mult_assoc in FACT.
  apply odd_and_even_dont_overlap in FACT; intuition.

  destruct y1.
  clear IHy2.
  replace (2^0) with 1 in FACT;[|unfold pow;nliamega].
  rewrite mult_1_l in FACT.
  unfold pow in FACT.
  fold pow in FACT.
  rewrite <- mult_assoc in FACT.
  apply odd_and_even_dont_overlap in FACT; intuition.

  remember (IHy2 y1) as HEREWEGO.
  assert (x1 = x2 /\ y1 = y2).
  apply HEREWEGO.
  clear IHy2 HEREWEGO HeqHEREWEGO.
  apply twice_two.
  rewrite mult_assoc.
  replace (2*2^y2) with (2^(S y2));[|unfold pow;nliamega].
  rewrite mult_assoc.
  replace (2*2^y1) with (2^(S y1));[|unfold pow;nliamega].
  auto.
  split;nliamega.
Qed.

Theorem Unfair_Pairing_to_fun :
  forall n x1 x2 y1 y2,
    Unfair_Pairing n x1 y1 ->
    Unfair_Pairing n x2 y2 ->
    (x1 = x2) /\ (y1 = y2).
Proof.
  intros n x1 x2 y1 y2 P1 P2.
  inversion P1; inversion P2; clear P1; clear P2; subst.
  apply unfair_unique; auto.
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

Program Fixpoint unfair_split_y (n : nat) {measure n} :=
  match n with
    | 0 => 0
    | S n' =>
      if (even_odd_dec n)
      then unfair_split_y (div2 n) + 1
      else 0
  end.

Program Fixpoint unfair_split_x (n : nat) {measure n} :=
  match n with
    | 0 => 0
    | S n' => 
      if (even_odd_dec n)
      then unfair_split_x (div2 n) 
      else div2 (n-1)
  end.

Lemma unfair_split_recombine : 
  forall n,
    n =
    ((2 ^ (unfair_split_y (S n))) * (2 * (unfair_split_x (S n)) + 1)) - 1.
Proof.
  intros n.
  apply (well_founded_ind
           lt_wf
           (fun n => n =
                     2 ^ unfair_split_y (S n) * (2 * unfair_split_x (S n) + 1)- 1)).
  clear n; intros n IND.

  remember (S n) as m.
  unfold_sub unfair_split_y (unfair_split_y m).
  fold unfair_split_y.
  unfold_sub unfair_split_x (unfair_split_x m).
  fold unfair_split_x.
  destruct m.
  intuition.
  rewrite Heqm; clear Heqm; clear m.

  destruct (even_odd_dec (S n)).
  destruct n.
  inversion e.
  inversion H0.
  
  simpl div2.

  replace (2 ^ (unfair_split_y (S (div2 n)) + 1)) with
  (2 * (2 ^ (unfair_split_y (S (div2 n)))));
    [|(replace (unfair_split_y (S (div2 n)) + 1) 
       with (S (unfair_split_y (S (div2 n))));[|omega]);
       simpl pow;
       nliamega].

  replace (2 * 2 ^ unfair_split_y (S (div2 n)) * (2 * unfair_split_x (S (div2 n)) + 1) - 1)
  with    (2 * (2 ^ unfair_split_y (S (div2 n)) * (2 * unfair_split_x (S (div2 n)) + 1)) - 1);[|nliamega].

  remember (2 ^ unfair_split_y (S (div2 n)) * (2 * unfair_split_x (S (div2 n)) + 1)) as m.
  destruct m.

  apply pow_S_prod_false in Heqm; intuition.

  replace (2 ^ unfair_split_y (S (div2 n)) * (2 * unfair_split_x (S (div2 n)) + 1)) 
  with ((2 ^ unfair_split_y (S (div2 n)) * (2 * unfair_split_x (S (div2 n)) + 1) - 1) + 1) in Heqm.
  rewrite <- (IND (div2 n)) in Heqm.
  rewrite Heqm; clear Heqm; clear m.
  unfold mult.
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

Lemma div2_bigger_than_fl_log : forall n, 8 <= n -> div2 n > fl_log n.
Proof.
  destruct n.
  intuition.
  destruct n.
  intuition.
  destruct n.
  intuition.
  destruct n.
  intuition.
  destruct n.
  intuition.
  destruct n.
  intuition.
  destruct n.
  intuition.
  destruct n.
  intuition.
  intros _.

  unfold div2; fold div2.
  rewrite fl_log_div2'.
  replace (div2 (S (S (S (S (S (S (S n)))))))) with (S (S (S (div2 (S n)))))
    by (unfold div2;auto).
  rewrite fl_log_div2'.
  replace (div2 (S (S (div2 (S n))))) with (S (div2 (div2 (S n))))
    by (unfold div2; auto).
  rewrite fl_log_div2'.
  repeat (apply gt_n_S).

  apply (well_founded_ind
           lt_wf
           (fun n =>  S (div2 n) > fl_log (div2 (div2 (div2 (S n)))))).
  clear n; intros n IND.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.

  replace (div2 (div2 (div2 (S (S (S (S (S (S (S (S (S (S n)))))))))))))
  with (S (div2 (div2 (div2 (S (S n)))))) by (unfold div2;auto).
  rewrite fl_log_div2'.
  replace (div2 (S (S n))) with (S (div2 n)) by (unfold div2;auto).
  apply gt_n_S.
  eapply (le_gt_trans _ (S (div2 (div2 n)))).

  replace (div2 (S (S (S (S (S (S (S (S (S n)))))))))) with
  (S (div2 (S (S (S (S (S (S (S n))))))))) by (unfold div2; auto).
  apply le_n_S.
  apply div2_monotone.
  remember (lt_div2' n).
  eapply (le_trans _ (S n)); nliamega.
  apply IND.
  apply (lt_le_trans _ (S n));auto.
  nliamega.
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Enum")) *)
(* end: *)
