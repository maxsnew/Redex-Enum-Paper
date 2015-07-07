Require Import Coq.Arith.Arith_base.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Div2 Coq.Arith.Even.
Require Import Coq.Lists.ListSet.

Require Import Enum.Enum Enum.Pairing Enum.Sets Enum.Trace.
Require Import Enum.EvenOddPow Enum.Util Enum.UnfairPairing.

(* read as f-fairness *)
Definition F_Fair2 {tout} (f : nat -> nat) (k : forall {ty1 ty2}, Enum ty1 -> Enum ty2 -> Enum (tout ty1 ty2)) :=
  forall n,
    let equilibrium := f n
    in match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat)) equilibrium with
         | Tracing l_uses r_uses _ _ =>
           n < equilibrium /\ l_uses ≃ r_uses
       end.

Definition Fair2 {tout} (k : forall ty1 ty2 : Set, Enum ty1 -> Enum ty2 -> Enum (tout ty1 ty2)) :=
  exists f, @F_Fair2 tout f k.

Definition F_Fair3 {tout} (f : nat -> nat) (k : forall {ty1 ty2 ty3}, Enum ty1 -> Enum ty2 -> Enum ty3 -> Enum (tout ty1 ty2 ty3)) :=
  forall n,
    let equilibrium := f n
    in 
    match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)) equilibrium with
      | Tracing z_uses o_uses t_uses _ =>
        n < equilibrium /\ z_uses ≃ o_uses /\ o_uses ≃ t_uses
    end.

Definition Fair3 {tout} (k : forall ty1 ty2 ty3, Enum ty1 -> Enum ty2 -> Enum ty3 -> Enum (tout ty1 ty2 ty3)) :=
  exists f, F_Fair3 f k.

Definition Fair4 {tout} (k : forall {ty1 ty2 ty3 ty4}, Enum ty1 -> Enum ty2 -> Enum ty3 -> Enum ty4 -> Enum (tout ty1 ty2 ty3 ty4)) :=
  forall n,
  exists equilibrium,
    match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat) (E_Trace three E_Nat)) equilibrium with
      | Tracing z_uses o_uses tw_uses th_uses =>
        n < equilibrium /\ z_uses ≃ o_uses /\ o_uses ≃ tw_uses /\ tw_uses ≃ th_uses
    end.

Definition AltUnfair3 {tout} (k : forall {ty1 ty2 ty3}, Enum ty1 -> Enum ty2 -> Enum ty3 -> Enum (tout ty1 ty2 ty3)) :=
  exists threshold,
    forall eq_cand,
      eq_cand > threshold ->
      match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)) eq_cand with
        | Tracing use0 use1 use2 _ =>
          (~ (use0 ≃ use1)) \/ (~ (use1 ≃ use2)) \/ (~ (use0 ≃ use2))
      end.

Theorem AltUnfair3Suff {tout} (k : forall {ty1 ty2 ty3}, Enum ty1 -> Enum ty2 -> Enum ty3 -> Enum (tout ty1 ty2 ty3)) : AltUnfair3 (@k) -> ~ (Fair3 (@k)).
Proof.
  unfold AltUnfair3, Fair3, F_Fair3, not.
  intros [thresh Halt] [f Hunf].
  specialize (Hunf (thresh)).
  specialize (Halt (f thresh)).
  destruct (Trace_lt (k _ _ _ (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat))
                     (f thresh)) as [t0 t1 t2 t3] in *.
  intuition.
  assert (t0 ≃ t2) by (eapply set_eq_trans; eauto); contradiction.
Qed.

Theorem F_Fair2_impl_Fair2 {tout} f (k : forall ty1 ty2 : Set, Enum ty1 -> Enum ty2 -> Enum (tout ty1 ty2)) :
  F_Fair2 f k -> Fair2 k.
Proof. unfold Fair2, F_Fair2; intuition; eauto. Qed.
Hint Resolve F_Fair2_impl_Fair2 : fair.

Theorem F_Fair3_impl_Fair3 {tout} f (k : forall ty1 ty2 ty3, Enum ty1 -> Enum ty2 -> Enum ty3 -> Enum (tout ty1 ty2 ty3)) :
  F_Fair3 f k -> Fair3 k.
Proof. unfold Fair3, F_Fair3; intuition; eauto. Qed.
Hint Resolve F_Fair3_impl_Fair3 : fair.

Section SumFair.
  Lemma Sum_precise
  : forall {tyl tyr} n (e1: Enum tyl) (e2: Enum tyr),
      Trace_lt (E_Sum e1 e2) (double n) ≡ (Trace_lt e1 n) ⊔ (Trace_lt e2 n).
  Proof.
    intros; induction n; [compute; tauto|];
    rewrite double_S; unfold Trace_lt at 1; fold (@Trace_lt (tyl + tyr)); unfold Trace_on;
    remember (Enumerates_from_dec (E_Sum e1 e2) (S (double n))) as Er; destruct Er as [[vr tr] Er];
    remember (Enumerates_from_dec (E_Sum e1 e2) (double n)) as El; destruct El as [[vl tl] El]; simpl;
    eapply trace_eq_trans; [apply trace_plus_assoc|];
    eapply trace_eq_trans; [apply trace_plus_cong; [apply trace_plus_comm | apply trace_eq_refl]|];
    eapply trace_eq_trans; [apply trace_eq_symm; apply trace_plus_assoc|];
    eapply trace_eq_trans; [apply trace_plus_cong; [apply trace_eq_refl|]; apply trace_plus_cong; [apply trace_eq_refl|]; apply IHn |];
    eapply trace_eq_trans; [apply trace_plus_cong; [apply trace_eq_refl| apply trace_plus_assoc]|];
    eapply trace_eq_trans; [apply trace_plus_cong; [apply trace_eq_refl| apply trace_plus_cong; [apply trace_plus_comm | apply trace_eq_refl]]|];
    eapply trace_eq_trans; [apply trace_plus_cong; [apply trace_eq_refl|apply trace_eq_symm; apply trace_plus_assoc ]|];
    eapply trace_eq_trans; [apply trace_plus_assoc|];
    apply trace_plus_cong; apply trace_plus_cong; [| apply trace_eq_refl | | apply trace_eq_refl];
    [ unfold Trace_on; destruct (Enumerates_from_dec e1 n) as [[x' t'] Henum']; simpl;
      clear HeqEr; clear dependent vr; clear tr HeqEl;
      invert_Enumerates; subst; even_odd_crush; subst; Eff; subst; apply trace_eq_refl
    | clear HeqEr HeqEl; unfold Trace_on;
      destruct (Enumerates_from_dec e2 n) as [[x' t'] Henum']; simpl;
      invert_Enumerates; subst; even_odd_crush; repeat subst;
      Eff; subst; apply trace_eq_refl
    ].
  Qed.

  (* Proof idea: equilibrium = 2 * n + 2,  uses = 0..(S n) *)
  Theorem SumFair_Linear : @F_Fair2 sum (fun n => double (S n)) (@E_Sum).
  Proof.
    unfold F_Fair2.
    intros n.
    remember (Trace_lt (E_Sum (E_Trace zero E_Nat) (E_Trace one E_Nat)) (double (S n))) as t; destruct t as [tz to ttw tth].
    split; [unfold double; nliamega| ].

    remember (Sum_precise (S n) (E_Trace zero E_Nat) (E_Trace one E_Nat)).
    apply set_eq_trans with (z_to_n (S n));
      [ replace tz with (trace_proj zero (Tracing tz to ttw tth)) by trivial
      | replace to with (trace_proj one (Tracing tz to ttw tth)) by trivial; apply set_eq_symm
      ];
      (eapply set_eq_trans; [apply trace_eq_proj; rewrite Heqt; eassumption|]).
    rewrite trace_proj_plus_distrl; rewrite (trace_lt_Nat_off _ zero one); [| discriminate].
    eapply set_eq_trans; [apply set_union_unitr | apply set_eq_symm; apply trace_lt_Nat].

    rewrite trace_proj_plus_distrl; rewrite (trace_lt_Nat_off _ one zero); [| discriminate].
    eapply set_eq_trans; [apply set_union_unitl | apply set_eq_symm; apply trace_lt_Nat].
  Qed.
  Hint Resolve SumFair_Linear : fair.

  Corollary SumFair : @Fair2 sum (@E_Sum).
  Proof. eauto with fair. Qed.
End SumFair.

Section NaiveSum3Unfair.
  Definition NaiveSum3 {ty1 ty2 ty3} (e1: Enum ty1) (e2: Enum ty2) (e3: Enum ty3) :=
    E_Sum e1 (E_Sum e2 e3).

  Notation x4 n := (double (double n)).
  
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
        rewrite <-even_double by assumption.
        apply even_double; assumption.
      + right; right; left; split; [| split]; try assumption.
        replace (double (double (div2 (div2 n))) + 2) with (S (S (double (double (div2 (div2 n)))))) by nliamega.
        rewrite <-double_S.
        rewrite <-odd_double by assumption.
        apply even_double; assumption.
    - destruct (even_odd_dec (div2 n)).
      + right; left; split; [| split]; try assumption.
        rewrite <-even_double by assumption.
        replace (double (div2 n) + 1) with (S (double (div2 n))) by nliamega.
        apply odd_double; assumption.
      + right; right; right; split; [| split]; try assumption.
        replace (double (double (div2 (div2 n))) + 3) with (S (S (S (double (double (div2 (div2 n))))))) by nliamega.
        rewrite <-double_S.
        rewrite <-odd_double by assumption.
        apply odd_double; assumption.
  Qed.

  Lemma div4big : forall n, n >= 8 -> (div2 (div2 n) >= 2).
  Proof.
    intros n ?; remember (n - 8) as k; replace n with (8 + k); simpl; nliamega.
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
    assert (div2 (div2 n) >= 2) by (apply div4big; assumption).
    repeat (rewrite <-double_twice).
    destruct (par4 n) as [[Hpar [? ?]] | [[Hpar [? ?]] | [[Hpar [? ?]] | [Hpar [? ?]]]]]; rewrite Hpar at 2; rewrite Hpar at 3.
    - clear H0; split.
      + rewrite double_twice; rewrite double_twice.
        apply mult_le_compat_l.
        rewrite <-even_div2 by assumption.
        unfold double.
        nliamega.
      + rewrite <-even_div2 by assumption.
        (repeat (rewrite double_twice)).
        nliamega.
    - split.
      + rewrite double_S.
        replace (double (double (div2 (div2 n))) + 1 ) with (S (double (double (div2 (div2 n))))) by nliamega.
        apply le_n_S.
        rewrite <-even_div2 by assumption.
        unfold double.
        nliamega.
      + rewrite <-even_div2 by assumption.
        replace (_ + 1) with (S (double (double (div2 (div2 n))))) by nliamega.
        unfold double; nliamega.
    - split.
      + rewrite double_S.
        rewrite double_S.
        rewrite <-odd_div2 by assumption.
        rewrite double_S.
        replace (double (double (div2 (div2 n))) + 2) with (S (S (double (double (div2 (div2 n)))))) by nliamega.
        repeat apply le_n_S.
        unfold double; nliamega.
      + rewrite <-odd_div2 by assumption.
        repeat rewrite double_S.
        nliamega.
    - split.
      + rewrite double_S.
        rewrite double_S.
        rewrite <-odd_div2 by assumption.
        rewrite double_S.
        replace (double (double (div2 (div2 n))) + 2) with (S (S (double (double (div2 (div2 n)))))) by nliamega.
        repeat apply le_n_S.
        unfold double; nliamega.
      + rewrite <-odd_div2 by assumption.
        repeat rewrite double_S.
        nliamega.
  Qed.

  Lemma SumSum_precise
  : forall n {ty1 ty2 ty3} (e1: Enum ty1) (e2: Enum ty2) (e3: Enum ty3),
      Trace_lt (E_Sum e1 (E_Sum e2 e3)) (double (double n))
      ≡ (Trace_lt e1 (double n)) ⊔ ((Trace_lt e2 n) ⊔ (Trace_lt e3 n)).
  Proof.
    intros.
    eapply trace_eq_trans; [apply Sum_precise|].
    apply trace_plus_cong; [apply trace_eq_refl|].
    apply Sum_precise.
  Qed.

  Definition NS3T := NaiveSum3 (E_Trace zero E_Nat)
                               (E_Trace one  E_Nat)
                               (E_Trace two  E_Nat).

  Lemma NS3Tl_precise
  : forall n,
      (trace_proj zero (Trace_lt NS3T (double n))) ≃ (z_to_n n).
  Proof.
    intros n.
    eapply set_eq_trans; [apply trace_eq_proj; apply Sum_precise|].
    rewrite trace_proj_plus_distrl.
    eapply set_eq_trans; [| apply set_union_unitr].
    apply set_union_cong.
    apply set_eq_symm; apply trace_lt_Nat.
    rewrite trace_lt_Sum_off; [apply set_eq_refl| | ]; (intros; rewrite trace_off; [trivial | discriminate ]).
  Qed.

  Lemma NS3Tr_precise
  : forall n,
      (trace_proj one (Trace_lt NS3T (double (double n)))) ≃ z_to_n n.
  Proof.
    intros n.
    eapply set_eq_trans; [apply trace_eq_proj; apply SumSum_precise|].
    eapply set_eq_trans; [apply trace_eq_proj; apply trace_plus_comm|].
    eapply set_eq_trans; [apply trace_eq_proj; apply trace_eq_symm; apply trace_plus_assoc|].
    rewrite trace_proj_plus_distrl.
    eapply set_eq_trans; [| apply set_union_unitr].
    apply set_union_cong; [apply set_eq_symm; apply trace_lt_Nat|].
    rewrite trace_proj_plus_distrl.
    repeat (rewrite trace_lt_Nat_off; [| discriminate]).
    compute; tauto.
  Qed.

  Theorem NaiveSum3Unfair : ~ (Fair3 (@NaiveSum3)).
  Proof.
    apply AltUnfair3Suff; unfold AltUnfair3; fold NS3T.
    exists 7.
    intros n H.
    remember (Trace_lt NS3T n) as t; destruct t as [s0 s1 s2 s4].
    assert (exists m p, 2 * m <= n < 4 * p /\ p < m) as [m [p [[Hmn Hnp] Hpn]]] by (apply div2div4; nliamega).
    left.
    
    assert (~ s0 ⊂ s1); [| intros [? ?]; contradiction ].

    assert ((z_to_n m) ⊂ s0).
    rewrite <-double_twice in *.
    replace s0 with (trace_proj zero (Trace_lt NS3T n)) by (rewrite <-Heqt; trivial).
    eapply subset_trans; [| apply sub_trace_proj; apply Trace_lt_sub; apply Hmn ].
    apply set_subset_weaken; apply set_eq_symm; apply NS3Tl_precise.
    
    assert (s1 ⊂ (z_to_n p)).
    replace (4 * p) with (double (double p)) in * by (simpl; unfold double; nliamega).
    replace s1 with (trace_proj one (Trace_lt NS3T n)) by (rewrite <-Heqt; trivial).
    eapply subset_trans.
    apply sub_trace_proj.
    apply (@Trace_lt_sub (nat + (nat + nat)) )with (n := double (double p)); nliamega.
    apply set_subset_weaken.
    apply NS3Tr_precise.
    
    intros Hcontra.
    eapply z_to_n_nosub; [apply Hpn|].
    repeat (eapply subset_trans; [eassumption|]); apply subset_refl.
  Qed.
End NaiveSum3Unfair.

Section PairFair.
  Definition E_PairNN := (E_Pair (E_Trace zero E_Nat) (E_Trace one E_Nat)).
  Lemma Pair_layer {tyl tyr} (e1: Enum tyl) (e2: Enum tyr) n
  : Trace_from_to (E_Pair e1 e2) (n * n) (S n * S n)
                  ≡ (Trace_lt e1 (S n)) ⊔ (Trace_lt e2 (S n)).
  Proof.
    apply trace_eq_eq'_equiv; split.
    (* trace (e1 x e2) n^2 (n+1)^2 < (trace ) *)
    (* TODO: come at this hard with some Ltac *)
    - apply sub_trace_In_equiv; intros x tg Hin;
      rewrite set_In_Trace_from_to in Hin by nliamega; destruct Hin as [k [[Hnnk HkSnSn] Hin]];
      unfold Trace_on in Hin;
      destruct (Enumerates_from_dec (E_Pair e1 e2) k) as [[v t] Henum]; simpl in Hin;
      invert_Enumerates; subst.
      destruct (sub_trace_In_equiv (lt ⊔ rt)
                                   ((Trace_lt e1 (S n)) ⊔ (Trace_lt e2 (S n)))).
      match goal with
        | [ H: context[_ -> _ ∈ trace_proj _ ?T ] |- _ ∈ trace_proj _ ?T ] => apply H; [| assumption]
      end;
      apply sub_trace_plus_cong;
      eapply Trace_lt_Enumerates; [| eassumption | | eassumption];
      destruct (Pairing_bound ln rn k n); auto.
    - eapply sub_trace_trans; [|apply trace_eq_weakenl; apply sub_trace_plus_eq; apply sub_trace_refl];
      apply sub_trace_plus_cong.
      (* trace e1 0..n+1 < trace (e1 x e2) n^2 (n+1)^2 *)
      + apply sub_trace_In_equiv; intros x tg Hin;
        rewrite set_In_Trace_lt in Hin by nliamega;
        destruct Hin as [k [Hkn Hin]];
        apply set_In_Trace_from_to; [nliamega|];
        destruct (le_lt_dec n k);
        [exists (k*k + k + n) | exists (k + n * n)];
        (split; [nliamega|]);
        unfold Trace_on; destruct (Enumerates_from_dec _ _) as [[v t] Henum]; simpl;
        invert_Enumerates;
        rewrite trace_proj_plus_distrl; apply set_union_intro1;
        [ assert (Pairing (k * k + k + n) k n) by (constructor; nliamega)
        | assert (Pairing (k + n * n) k n) by (constructor; nliamega)];
        rewrite_pairing_to_fun; get_trace_ons; subst; auto.
      + apply sub_trace_In_equiv; intros x tg Hin;
        rewrite set_In_Trace_lt in Hin by nliamega;
        destruct Hin as [k [Hkn Hin]];
        apply set_In_Trace_from_to; [nliamega|];
        destruct (le_lt_dec k n);
        [exists (n * n + n + k) | exists (n + k * k)]; (split; [nliamega|]);
        unfold Trace_on; destruct (Enumerates_from_dec _ _) as [[v t] Henum]; simpl;
        invert_Enumerates;
        rewrite trace_proj_plus_distrl; apply set_union_intro2;
        [ assert (Pairing (n * n + n + k) n k) by (constructor; nliamega)
        | assert (Pairing (n + k * k) n k) by (constructor; nliamega) ];
        rewrite_pairing_to_fun; get_trace_ons; subst; auto.
  Qed.

  Lemma PairNN_layer :
    forall n,
      Trace_from_to E_PairNN (n * n) (S n * S n)
      ≡ Tracing (z_to_n (S n)) (z_to_n (S n)) ∅ ∅.
  Proof.
    intros n.
    eapply trace_eq_trans.
    unfold E_PairNN; apply Pair_layer.
    apply trace_eq_symm.
    apply trace_eq_trans with ((Tracing (z_to_n (S n)) ∅ ∅ ∅)
                                 ⊔ (Tracing ∅ (z_to_n (S n)) ∅ ∅)).
    remember (S n) as k; unfold trace_plus; split4; auto; apply set_eq_symm; apply set_union_unitl.
    apply trace_plus_cong; rewrite trace_proj_reconstruct.
    split4; [ apply trace_lt_Nat | | | ]; rewrite trace_lt_Nat_off by discriminate; auto.
    split4; [ | apply trace_lt_Nat | | ]; rewrite trace_lt_Nat_off by discriminate; auto.
  Qed.      

  Lemma Pair_precise
  : forall n {ty1 ty2} e1 e2,
      (Trace_lt (@E_Pair ty1 ty2 e1 e2) (n * n)) ≡ ((Trace_lt e1 n) ⊔ (Trace_lt e2 n)).
    intros n.
    induction n as [| n IHn]; [  intros; compute; tauto| ].
    intros.
    eapply trace_eq_trans.
    apply trace_from_to_0_split with (m := n * n) (n := S n * S n); nliamega.
    eapply trace_eq_trans; [apply sub_trace_plus_eq| apply Pair_layer].
    eapply sub_trace_trans; [| apply trace_eq_weakenl; apply trace_eq_symm; apply Pair_layer ].
    eapply sub_trace_trans; [apply trace_eq_weakenl; apply IHn|].
    apply sub_trace_plus_cong; apply Trace_lt_sub; nliamega.
  Qed.

  Lemma PairPair_precise
  : forall {ty1 ty2 ty3} n e1 e2 e3,
      Trace_lt (@E_Pair ty1 _ e1 (@E_Pair ty2 ty3 e2 e3)) ((n * n) * (n * n))
               ≡ (Trace_lt e1 (n * n)) ⊔ ((Trace_lt e2 n) ⊔ (Trace_lt e3 n)).
  Proof.
    intros.
    eapply trace_eq_trans; [apply Pair_precise|].
    apply trace_plus_cong; [apply trace_eq_refl| ].
    apply Pair_precise.
  Qed.

  Lemma Pair_Fair_precise :
    forall n, Trace_lt E_PairNN (n * n) ≡ Tracing (z_to_n n) (z_to_n n) ∅ ∅.
  Proof.
    induction n.
    compute; tauto.
    apply trace_eq_trans
    with (t2 := ((Trace_lt E_PairNN (n * n)) ⊔ (Trace_from_to E_PairNN (n * n) (S n * S n)))).
    apply trace_from_to_0_split; nliamega.
    apply trace_eq_trans with (t2 := ((Tracing (z_to_n n) (z_to_n n) ∅ ∅)
                                        ⊔ (Tracing (z_to_n (S n)) (z_to_n (S n)) ∅ ∅))).
    apply trace_plus_cong; auto.
    apply PairNN_layer.
    apply trace_eq_trans with (t2 := (Tracing (z_to_n (S n)) (z_to_n (S n))) ∅ ∅).
    unfold trace_eq.
    split4;
      [ (apply subset_union_eq; unfold z_to_n at 2; fold z_to_n; apply set_subset_add; apply subset_refl)
      | (apply subset_union_eq; unfold z_to_n at 2; fold z_to_n; apply set_subset_add; apply subset_refl)
      | apply set_eq_refl
      | apply set_eq_refl ].

    apply trace_eq_refl.
  Qed.

  Theorem PairFairSquare : @F_Fair2 prod (fun n => (S n) * (S n)) (@E_Pair).
  Proof.    
    unfold F_Fair2, Fair2.
    intros n.
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
  Hint Resolve PairFairSquare : fair.

  Theorem PairFair : @Fair2 prod (@E_Pair).
  Proof. eauto with fair. Qed.
End PairFair.

Section NaiveTripleUnfair.

  Definition NaiveTriple3 {ty1 ty2 ty3} e1 e2 e3 :=
    @E_Pair ty1 _ e1 (@E_Pair ty2 ty3 e2 e3).

  Definition traceNP3 := Trace_lt (NaiveTriple3 (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)).

  Definition NP3T := NaiveTriple3 (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat).

  Theorem NaiveTripleUnfair : ~ (Fair3 (@NaiveTriple3)).
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
    assert (~ t0 ⊂ t1); [ | intros []; contradiction].

    assert ((z_to_n m) ⊂ t0).
    - remember (Trace_lt NP3T (m * m)) as t; destruct t as [mm0 mm1 mm2 mm3].
      assert ((Trace_lt NP3T (m * m)) ⊏ (Trace_lt NP3T n))
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
      remember (((Trace_lt (E_Trace zero E_Nat) m) ⊔ (Trace_lt (E_Pair (E_Trace one E_Nat) (E_Trace two E_Nat)) m))).
      destruct t0.
      replace mm0 with (trace_proj zero (Tracing mm0 mm1 mm2 mm3)) by auto.
      eapply subset_trans; [| apply trace_eq_proj;  eassumption].
      rewrite Heqt1.
      rewrite trace_proj_plus_distrl.
      apply subset_union_transl.
      apply trace_lt_Nat.

    - assert (t1 ⊂ (z_to_n p)).
      remember (Trace_lt NP3T ((p * p) * (p * p))) as p4t.
      assert ((Trace_lt NP3T n) ⊏ p4t) by (subst; apply Trace_lt_sub; auto; nliamega).
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

Section Unfair_Unfair.

  Definition UPTN := (E_Unfair_Pair (E_Trace zero E_Nat) (E_Trace one E_Nat)).

  Lemma Trace_on_UPTN :
    forall n s0 s1 s2 s3,  
      Tracing s0 s1 s2 s3 = Trace_on UPTN n -> 
      exists x y,
        n = (2 ^ y * (2 * x + 1) - 1) /\ 
        s0 = (x :: nil)%list /\ 
        s1 = (y :: nil)%list.
  Proof.
    intros n s0 s1 s2 s3 TR.
    unfold Trace_on in TR.
    unfold Enumerates_from_dec in TR; simpl in TR.
    remember (Unfair_Pairing_from_dec n) as UPn.
    remember (unfair_split_recombine n).
    clear HeqUPn Heqe.
    remember (unfair_split_x (S n)) as x.
    remember (unfair_split_y (S n)) as y.
    unfold trace_plus in TR.
    inversion TR.
    exists x.
    exists y.
    auto.
  Qed.

  Lemma Unfair_Pair_right_precise : 
    forall n, trace_proj zero (Trace_lt UPTN n) ≃ (z_to_n (div2 (S n))).
  Proof.
    apply (well_founded_ind
             lt_wf
             (fun n => trace_proj zero (Trace_lt UPTN n) ≃ z_to_n (div2 (S n)))).

    intros n IND.
    destruct n.

    (* n=0 *) 
    simpl; auto.

    unfold Trace_lt; fold @Trace_lt.

    destruct n.

    (* n=1 *)
    clear IND.
    simpl.
    unfold Trace_on.
    unfold Enumerates_from_dec; simpl.
    remember (Unfair_Pairing_from_dec 0) as UP0; clear HeqUP0.
    destruct UP0 as [[x y] u].
    simpl fst in *; simpl snd in *.
    unfold trace_proj.
    unfold trace_plus.
    simpl.
    assert (x=0);[|subst;auto].
    inversion u; subst.
    remember (2 ^ y * (x + (x + 0) + 1)) as n.
    replace (x+(x+0)+1) with ((2*x)+1) in Heqn;[|nliamega].
    destruct n.
    apply pow_S_prod_false in Heqn; intuition.
    assert(S n=1) as SNone;[nliamega|].
    rewrite SNone in *.
    simpl.
    assert (y=0).
    apply (odds_have_no_powers_of_two x).
    rewrite <- Heqn.
    repeat constructor; auto.
    subst.
    nliamega.

    (* inductive case *)
    replace (div2 (S (S (S n)))) with (S (div2 (S n))); [|unfold div2;auto].

    unfold trace_plus.
    remember (Trace_on UPTN (S n)) as X1; destruct X1.
    remember (Trace_lt UPTN (S n)) as X2; destruct X2.
    unfold trace_proj.

    unfold Trace_lt in HeqX2; fold @Trace_lt in HeqX2.
    remember (Trace_on UPTN n) as TonN.
    remember (Trace_lt UPTN n) as TltN.
    unfold trace_plus in HeqX2.
    destruct TonN.
    destruct TltN.
    inversion HeqX2; subst;clear HeqX2.
    
    apply Trace_on_UPTN in HeqX1.
    destruct HeqX1 as [SNx [SNy [SNeq [Seq s0eq]]]].
    apply Trace_on_UPTN in HeqTonN.
    destruct HeqTonN as [Nx [Ny [Neq [s7eq s8eq]]]].
    subst s s7.
    clear s1 s2 s9 s10 s0eq s0 s8 s8eq.

    assert (trace_proj zero (Trace_lt UPTN n) ≃ z_to_n (div2 (S n))) as S11EQN;
      [apply IND; auto|clear IND].
    rewrite <- HeqTltN in S11EQN.
    unfold trace_proj in S11EQN.
    clear HeqTltN s12 s13 s14.

    apply (set_eq_trans ((SNx :: nil)%list ∪ ((Nx :: nil)%list ∪ s11))
                        ((SNx :: nil)%list ∪ ((Nx :: nil)%list ∪ (z_to_n (div2 (S n)))))).
    repeat (apply set_union_cong); auto.
    clear s11 S11EQN.

    destruct n.
    assert (Ny = 0). 
    remember (2 ^ Ny * (2 * Nx + 1)) as n.
    destruct n.
    apply pow_S_prod_false in Heqn; intuition.
    assert (n=0). nliamega.
    subst n.
    symmetry in Heqn.
    apply (odds_have_no_powers_of_two Nx).
    rewrite Heqn.
    repeat constructor; auto.

    (* confusion here! *)
    assert (SNx = 0).
    assert (2 = 2 ^ SNy * (2 * SNx + 1)); nliamega.

    simpl.
    destruct (eq_nat_dec Nx SNx); subst; auto; intuition.
    simpl in Neq.
    assert (Nx=0).
    nliamega.
    intuition.

    assert (S (S (S n)) = 2 ^ SNy * (2 * SNx + 1)) as SSSNeq;[nliamega|clear SNeq].
    assert (S (S n) = 2 ^ Ny * (2 * Nx + 1)) as SSNeq;[nliamega|clear Neq].

    destruct (even_odd_dec n).

    (* even case *)
    assert (SNy=0).
    assert (odd (S (S (S n))));[repeat constructor; auto|].
    apply (odds_have_no_powers_of_two SNx SNy).
    rewrite SSSNeq in H; auto.
    subst SNy.
    unfold pow in SSSNeq; rewrite mult_1_l in SSSNeq.
    assert ((2 * SNx) = S (S n)) as SNx2.
    nliamega.
    unfold z_to_n; fold z_to_n.
    rewrite <- SNx2.
    rewrite div2_double.
    constructor.
    
    apply subset_union_both; auto.
    apply subset_union_both.
    assert (Nx < div2 (2 ^ Ny * (2 * Nx + 1))).
    apply even_prod_lt.
    rewrite <- SSNeq.
    repeat constructor; auto.
    rewrite <- SSNeq in H.
    rewrite <- SNx2 in H.
    rewrite div2_double in H.
    replace (set_add' SNx (z_to_n SNx)) with (z_to_n (S SNx));[|unfold z_to_n;auto].
    apply subset_In_equiv; intros x IN.
    apply z_to_n_correct.
    destruct IN as [EQ|ELE].
    nliamega.
    inversion ELE.

    apply set_subset_add; auto.
    apply set_add_subset.
    apply (subset_In SNx (cons SNx nil));auto.
    apply subset_union_transl; auto.
    apply subset_union_transr.
    apply subset_union_transr.
    auto.

    (* odd case *)

    assert (Ny=0).
    apply (odds_have_no_powers_of_two Nx Ny).
    rewrite <- SSNeq.
    repeat constructor; auto.
    subst Ny.
    unfold pow in SSNeq; rewrite mult_1_l in SSNeq.
    assert ((2*Nx) = S n) as Nx2;[nliamega|].

    constructor.

    replace (S (div2 (S (S n)))) with (div2 (S (S (S n))));
      [|rewrite <- odd_div2;repeat constructor;auto].

    assert (SNx < (div2 (2 ^ SNy * (2 * SNx + 1)))) as questionable.
    apply even_prod_lt.
    rewrite <- SSSNeq.
    repeat constructor;auto.

    apply subset_union_both; auto.
    rewrite <- SSSNeq in questionable.
    apply subset_In_equiv; intros x IN.
    apply z_to_n_correct.
    destruct IN as [EQ|ELE].
    nliamega.
    destruct ELE.

    apply subset_union_both; auto.
    apply subset_In_equiv; intros x IN.
    destruct IN as [EQ|ELE];[|destruct ELE].
    subst x.
    apply z_to_n_correct.
    rewrite <- Nx2.
    unfold div2; fold div2.
    rewrite div2_double.
    auto.
    replace (div2 (S (S (S n)))) with (S (div2 (S (S n))));
      [|apply odd_div2; repeat constructor; auto].
    unfold z_to_n; fold z_to_n.
    apply set_subset_add;auto.
    unfold z_to_n; fold z_to_n.
    apply set_add_subset.
    rewrite <- even_div2 at 1; [|repeat constructor;auto].
    rewrite <- Nx2.
    rewrite div2_double.
    apply elem_union.
    apply (subset_In Nx ((Nx :: nil)%list)); auto.
    apply subset_union_transl; auto.
    apply subset_union_transr; auto.
    apply subset_union_transr; auto.
  Qed.

  Lemma Unfair_Pair_left_precise : 
    trace_proj one (Trace_lt UPTN 0) ≃ ∅ /\
    forall n, trace_proj one (Trace_lt UPTN (S n)) ≃ (z_to_n (S (fl_log n))).
  Proof.
    constructor.
    simpl; auto.
    apply (well_founded_ind
             lt_wf
             (fun n => trace_proj one (Trace_lt UPTN (S n)) ≃ z_to_n (S (fl_log n)))).
    intros n IND.
    destruct n.

    (* n = 0 *)
    unfold Trace_lt.
    unfold trace_proj.
    unfold trace_plus.
    remember ε as EMPTY.
    destruct EMPTY.
    inversion HeqEMPTY.
    remember (Trace_on UPTN 0) as TO0.
    destruct TO0.
    apply Trace_on_UPTN in HeqTO0.
    destruct HeqTO0 as [x [y [EQ [S3EQ S4EQ]]]].
    subst.
    clear HeqEMPTY.

    remember (2 ^ y * (2 * x + 1)) as n.
    destruct n.
    apply pow_S_prod_false in Heqn.
    intuition.
    assert (n=0) by nliamega.
    subst n.
    assert (y=0).
    apply (odds_have_no_powers_of_two x).
    rewrite <- Heqn.
    constructor.
    constructor.
    subst.
    simpl.
    unfold fl_log; simpl; auto.

    (* n =/= 0 *)
    replace (Trace_lt UPTN (S (S n)))
    with (Trace_on UPTN (S n) ⊔ (Trace_lt UPTN (S n))) ;[|unfold Trace_lt;auto].
    rewrite fl_log_div2'.
    unfold trace_plus.
    unfold trace_proj.
    remember (Trace_on UPTN (S n)) as TOnSn.
    remember (Trace_lt UPTN (S n)) as TLtSn.
    destruct TOnSn.
    destruct TLtSn.
    assert (trace_proj one (Trace_lt UPTN (S n)) ≃ z_to_n (S (fl_log n))) as TLT;
      [apply IND;auto|clear IND].
    unfold trace_proj in TLT.
    rewrite <- HeqTLtSn in TLT.
    apply (set_eq_trans (s0 ∪ s4) (s0 ∪ z_to_n (S (fl_log n)))).
    apply set_union_cong; auto.
    clear TLT HeqTLtSn.
    apply Trace_on_UPTN in HeqTOnSn.
    destruct HeqTOnSn as [x [y [Sneq [seq s0eq]]]].
    subst s0.
    clear s s1 s2 seq s3 s4 s5 s6.
    assert (S (S n) = 2 ^ y * (2 * x+1)) as SSneq;[nliamega|clear Sneq].

    destruct (pow_dec (S (S n))).
    (* is a power of two *)
    destruct s as [m SSneq'].
    assert (x=0) by (apply (power_of_two_and_odd_equality m y); nliamega).
    subst x.
    simpl in SSneq.
    rewrite mult_1_r in SSneq.
    clear SSneq' m.

    destruct y.
    unfold pow in SSneq.
    assert False; intuition.

    assert (n=2^(S y) - 2) by nliamega.
    replace (fl_log n) with y by (subst n; symmetry; apply fl_log_pow').
    rewrite <- fl_log_div2'.
    subst n.
    replace (S (2 ^ S y - 2)) with (2 ^ S y - 1) by nliamega.
    rewrite <- fl_log_pow''.
    replace (z_to_n (S (S y))) with (set_add' (S y) (z_to_n (S y)))
      by (unfold z_to_n; fold z_to_n; auto).
    eapply (set_eq_trans _ (cons (S y) (z_to_n (S y)))); auto.
    eapply (set_eq_trans _ (app (cons (S y) nil) (z_to_n (S y)))); auto.
    apply set_union_app_eq.

    (* is not a power of two *)
    rewrite <- fl_log_div2'.
    rewrite <-  fl_log_add1_when_not_power_of_two_doesnt_matter; auto.
    apply subset_union_eq.
    apply subset_In_def.
    intros ele IN.
    destruct IN.
    subst ele.
    apply z_to_n_correct.

    destruct n.
    remember (n0 1) as BAD.
    simpl in BAD; intuition.
    assert (S n = 2 ^ y * (2 * x + 1) - 2) by nliamega.
    rewrite H.
    destruct x.
    remember (n0 y).
    intuition.
    remember (bound_on_y_in_unfair_pair x y).
    nliamega.
    destruct H.
  Qed.

  Theorem Unfair_Pair_Unfair : ~ (@Fair2 prod (@E_Unfair_Pair)).
  Proof.
    unfold Fair2.
    unfold F_Fair2.
    intro THING; destruct THING as [f THING2].
    remember (THING2 8) as UNLIKELY; clear THING2 HeqUNLIKELY. 
    remember (Trace_lt
                (E_Unfair_Pair (E_Trace zero E_Nat) (E_Trace one E_Nat))
                (f 8)) as TRACING; destruct TRACING as [s0 s1 s2 s3].
    remember (f 8) as n; clear Heqn f; destruct UNLIKELY as [LB UNLIKELY].
    remember (E_Unfair_Pair (E_Trace zero E_Nat) (E_Trace one E_Nat)) as UPTN.

    assert (s1 = trace_proj one (Trace_lt UPTN n)).
    unfold trace_proj.
    destruct (Trace_lt UPTN n).
    inversion HeqTRACING.
    auto.

    assert (s0 = trace_proj zero (Trace_lt UPTN n)).
    unfold trace_proj.
    destruct (Trace_lt UPTN n).
    inversion HeqTRACING.
    auto.
    subst s0 s1.
    destruct n.
    intuition.
    assert (z_to_n (S (fl_log n)) ≃ z_to_n (div2 (S (S n)))) as ZTONUNLIKELY.
    eapply (set_eq_trans _ (trace_proj one (Trace_lt UPTN (S n)))); auto.
    apply set_eq_symm.
    destruct Unfair_Pair_left_precise as [_ B].
    subst UPTN; apply (B n).
    eapply (set_eq_trans _ (trace_proj zero (Trace_lt UPTN (S n)))); auto.
    apply set_eq_symm; auto.
    subst UPTN; apply Unfair_Pair_right_precise.
    clear UPTN HeqUPTN HeqTRACING UNLIKELY.
    destruct ZTONUNLIKELY as [_ UNLIKELYSUBSET].
    generalize UNLIKELYSUBSET.
    assert (not (z_to_n (div2 (S (S n))) ⊂ z_to_n (S (fl_log n)))); auto.
    eapply (not_subset_In_def _ _ (div2 n)).
    apply z_to_n_correct; auto.
    unfold not; intros UNLIKELYLT.
    apply z_to_n_correct in UNLIKELYLT.
    assert (8<=n) as EIGHTN by nliamega.
    apply div2_bigger_than_fl_log in EIGHTN.
    intuition.
  Qed.

End Unfair_Unfair.

(* Local Variables: *)
(* coq-load-path: (("." "Enum")) *)
(* end: *)
