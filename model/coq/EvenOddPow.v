Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Arith_base Coq.Arith.Even Coq.Arith.Div2.
Require Import Psatz.
Require Import Coq.Program.Wf Init.Wf.
Require Import Enum.Util.
Include WfExtensionality.


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

Lemma lt_div2'' : forall n,  div2 (S n) < S n.
Proof.
  apply (ind_0_1_SS (fun n => div2 (S n) < S n));
  intros; simpl; try simpl in H; omega.
Qed.
Hint Resolve lt_div2''.

Program Fixpoint fl_log n {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S n' => S (fl_log (div2 n'))
  end.

Lemma fl_log_div2' : 
  forall n,
    fl_log (S n) = S (fl_log (div2 n)).
Proof.
  intros.
  unfold_sub fl_log (fl_log (S n)); auto.
Qed.

Lemma div2_SSn : forall n, div2 (S (S n)) = S (div2 n).
Proof.
  unfold div2;auto.
Qed.

Lemma fl_log_zero : fl_log 0 = 0.
Proof.
  unfold_sub fl_log (fl_log 0); auto.
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

Lemma pow_S_prod_false : forall n m, 0 = (pow 2 n) * (m + 1) -> False.
Proof.
  intros n m FACT.
  destruct (mult_is_O (2 ^ n) (m + 1)) as [ZERO|ZERO]; auto.
  apply pow_not_zero in ZERO; intuition.
  replace (m+1) with (S m);nliamega.
Qed.

Lemma twice_two : forall x y, 2*x = 2*y -> x = y.
Proof.
  intros; nliamega.
Qed.

Lemma even_is_double : forall n, even (double n).
Proof.
  induction n.
  unfold double; simpl; constructor.
  replace (S n) with (n+1);[|omega].
  rewrite double_plus.
  unfold double at 2; simpl.
  replace (double n + 2) with (S (S (double n)));[|omega].
  constructor.
  constructor.
  auto.
Qed.


Lemma times_two_is_even : forall n, even (2*n).
Proof.
  intros.
  replace (2 * n) with (double n) by (unfold double;nliamega).
  apply even_is_double.
Qed.

Lemma odd_and_even_dont_overlap:
  forall n m, 2 * n = 2 * m + 1 -> False.
Proof.
  intros n m FACT.

  assert (odd (2*m+1)) as ODD.
  replace (2*m+1) with (S (2*m)) by nliamega.
  constructor.
  apply times_two_is_even.

  assert (even (2*n)) by (apply times_two_is_even).
  
  rewrite FACT in *.
  apply (not_even_and_odd (2*m+1)); auto.
Qed.

Lemma odds_have_no_powers_of_two : forall x y, odd (2 ^ y * (2 * x + 1)) -> y = 0.
Proof.
  intros x y OD.
  destruct y; auto.
  unfold pow in OD; fold pow in OD.
  replace (2 * 2 ^ y * (2 * x + 1)) with (double (2 ^ y * (2 * x + 1))) in OD;
    [|unfold double;nliamega].
  remember (2 ^ y * (2 * x + 1)) as n.
  assert (even (double n)).
  apply even_is_double.
  assert False;[|intuition].
  apply (not_even_and_odd (double n));auto.
Qed.

Lemma even_prod_lt : 
  forall x y, even (2^y * (2 * x + 1)) -> x < div2 (2^y * (2 * x + 1)).
Proof.
  intros x y EV.
  remember (2^y * (2 * x + 1)) as n; rename Heqn into NEQ.
  destruct y.
  unfold pow in NEQ.
  rewrite mult_1_l in NEQ.
  assert (odd n).
  replace (2*x+1) with (S (2*x)) in NEQ;[|nliamega].
  subst n.
  constructor.
  replace (2*x) with (double x);[|unfold double;nliamega].
  apply even_is_double.
  assert False;[|intuition].
  apply (not_even_and_odd n); auto.
  unfold pow in NEQ; fold pow in NEQ.
  subst n.
  rewrite <- mult_assoc.
  rewrite div2_double.
  assert (2^y >= 1);[|nliamega].
  clear x EV.
  induction y; try (unfold pow; fold pow);nliamega.
Qed.

Lemma pow2_not_odd :
  forall n m,
    odd n -> n=1 \/ (2^m <> n).
Proof.
  destruct 1.
  destruct H.
  auto.
  assert (odd (S (S n))) by (repeat constructor;auto).
  destruct m.
  intuition discriminate.
  unfold pow; fold pow.
  assert (even (2 * 2^m)) by apply times_two_is_even.
  right.
  unfold not.
  intros EQ.
  rewrite EQ in H1.
  apply (not_even_and_odd (S (S n))); auto.
Qed.
  
Lemma pow_dec :
  forall n, sumor {m | 2^m = n} (forall m, ~ 2^m = n).
Proof.
  apply (well_founded_induction
           lt_wf
           (fun n => (sumor {m | 2 ^ m = n} (forall m, ~2 ^ m = n)))).
  intros n REC.
  destruct n.

  (* zero *)
  right.
  unfold not.
  intros n BAD.
  apply pow_not_zero in BAD; intuition.

  (* non zero *)
  destruct (even_odd_dec (S n)).
  destruct (REC (div2 (S n))); auto; clear REC.

  (* even, div2 is is a power of two *)
  left.
  destruct s as [m meq].
  exists (S m).
  unfold pow; fold pow.
  rewrite meq.
  replace (2*div2 (S n)) with (double (div2 (S n)));
    [|unfold double; unfold mult;auto].
  rewrite even_double;auto.

  (* even, div2 is not a power of two *)
  right.
  unfold not.
  intros m TWOMSN.
  assert (div2 (2^m) = div2(S n)) as DIV2 by (rewrite TWOMSN;auto).
  rewrite <- DIV2 in n0.
  apply (n0 (m-1)).
  destruct m.
  unfold pow in *; fold pow in *.
  assert (n=0) by nliamega; subst n.
  inversion e.
  inversion H0.
  replace (S m - 1) with m by nliamega.
  unfold pow; fold pow.
  rewrite div2_double.
  auto.

  (* odd *)
  clear REC.
  destruct n.
  left.
  exists 0.
  simpl; auto.
  right.
  intros m NEQ.
  apply (pow2_not_odd (S (S n)) m) in o.
  destruct o; intuition.
Qed.

Lemma unique_pow_of_two : forall y y', 2^y = 2^y' -> y=y'.
Proof.
  induction y.

  (* y=0 *)
  unfold pow; fold pow.
  destruct y'; auto.
  intros FACT.
  assert False;[|intuition].
  apply (not_even_and_odd 1).
  rewrite FACT.
  unfold pow; fold pow.
  apply times_two_is_even.
  repeat constructor.

  (* y =/= 0 *)
  intros y' FACT.
  destruct y'.

  (* y' = 0 *)
  unfold pow in FACT; fold pow in FACT.
  assert False;[|intuition].
  apply (not_even_and_odd 1).
  rewrite <- FACT.
  apply times_two_is_even.
  repeat constructor.

  (* y' =/= 0 *)
  unfold pow in FACT; fold pow in FACT.
  assert (2^y = 2^y') by nliamega.
  apply IHy in H.
  nliamega.
Qed.

Lemma powers_of_two_have_no_odd_factors :
  forall y' y n, odd n -> 2^y = 2^y' * (S (S n)) -> False.
Proof.
  intros y' y n ODDn FACT.
  generalize dependent y'.
  induction y.
  unfold pow; fold pow.
  intros; nliamega.
  intro y'.
  destruct y'.
  unfold pow; fold pow.
  intros FACT.
  apply (not_even_and_odd (S (S n))).
  rewrite mult_1_l in FACT.
  rewrite <- FACT.
  apply times_two_is_even.
  constructor.
  constructor.
  auto.
  unfold pow; fold pow.
  intros FACT.
  assert (2^y = 2^y' * (S (S n))) as SIMPLERFACT by nliamega; clear FACT.
  apply IHy in SIMPLERFACT; intuition.
Qed.

Lemma power_of_two_and_odd_equality :
  forall y' y x,
    2 ^ y' = 2 ^ y * (2*x+1) -> x=0.
Proof.
  intros y' y x.
  destruct x; auto.
  intros.
  assert (odd (2 * S x + 1)).
  replace (2 * S x + 1) with (S (2 * S x)) by nliamega.
  constructor.
  apply times_two_is_even.
  replace (2 * S x + 1) with (S (S (2*x+1))) in * by nliamega.
  apply powers_of_two_have_no_odd_factors in H; auto.
  intuition.
  inversion H0.
  inversion H2.
  simpl;auto.
Qed.

Lemma fl_log_pow : forall n, (fl_log (2^(S n))) = (S n).
Proof.
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
  admit.
Qed.

Lemma fl_log_pow' : forall n, (fl_log (2^(S n) - 2)) = n.
Proof.
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
(*
  apply (well_founded_ind
           lt_wf
           (fun n => (fl_log (2^(S n) - 2)) = n)).
*)
  admit.
Qed.

Lemma fl_log_pow'' : forall n, S n = fl_log (2^(S n) - 1).
Proof.
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
  admit.
Qed.

Lemma fl_log_add1_when_not_power_of_two_doesnt_matter:
  forall n,
    (forall m, 2 ^ m <> S (S n)) ->
    fl_log n = fl_log (S n).
Proof.
  intros n FACT.
  destruct n.
  remember (FACT 1) as THING; simpl in THING; intuition.
  destruct n.
  compute; auto.
  destruct n.
  remember (FACT 2) as THING; simpl in THING; intuition.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  compute; auto.
  destruct n.
  remember (FACT 3) as THING; simpl in THING; intuition.
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
  admit.
Qed.

Lemma fl_log_add1_when_big_enough_and_even_doesnt_matter:
  forall n,
    fl_log (S (S (2 * n))) = fl_log (S (2 * n)).
Proof.
  intros.
  destruct n.
  compute; auto.
  replace (2 * S n) with (S (S (2 * n))) by nliamega.
  replace (fl_log (S (S (S (2 * n))))) with (S (fl_log (div2 (S (S (2 * n))))))
    by (rewrite fl_log_div2'; auto).
  rewrite fl_log_div2'.
  repeat (rewrite div2_SSn).
  rewrite div2_double.
  destruct n.
  compute; auto.
  replace (S (2 * S n)) with (S (S (S (2*n)))) by nliamega.
  rewrite div2_SSn.
  replace (div2 (S (2*n))) with (div2 (2*n))
    by (rewrite <- even_div2; auto; apply times_two_is_even).
  rewrite div2_double.
  auto.
Qed.
  
Lemma fl_log_double :
  forall n,
    fl_log (2*(S n)) = S (fl_log (S n - 1)).
Proof.
  intros n.
  replace (S n - 1) with n by nliamega.
  replace n with (div2 (2 * n)) at 2 by (rewrite div2_double;auto).
  rewrite <- fl_log_div2'.
  replace (2 * S n) with (S (S (2 * n))) by nliamega.
  apply fl_log_add1_when_big_enough_and_even_doesnt_matter.
Qed.

Lemma bound_on_y_in_unfair_pair :
  forall x y,
    y < fl_log (2 ^ y * (2 * (S x) + 1) - 2).
Proof.
  induction y.
  unfold pow.
  rewrite mult_1_l.
  replace (2*S x + 1 - 2) with (S (2*x)) by nliamega.
  rewrite fl_log_div2'.
  nliamega.

  unfold pow; fold pow.
  replace (2 * 2 ^ y * (2 * S x + 1) - 2) 
  with (2 * (2 ^ y * (2 * S x + 1) - 1)) by nliamega.
  remember (2 ^ y * (2 * S x + 1) - 1) as m.
  destruct m.
  remember (2 ^ y * (2 * S x + 1)) as m.
  destruct m.

  simpl in IHy.
  rewrite fl_log_zero in IHy.
  intuition.

  assert (m=0) by nliamega.
  subst m.
  simpl in IHy.
  rewrite fl_log_zero in IHy.
  intuition.
  rewrite fl_log_double.
  rewrite Heqm.
  replace (2 ^ y * (2 * S x + 1) - 1 - 1) with (2 ^ y * (2 * S x + 1) - 2) by nliamega.
  nliamega.
Qed.
