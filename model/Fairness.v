Require Import Coq.Arith.Arith_base.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Div2 Coq.Arith.Even.
Require Import Coq.Lists.ListSet.

Require Import Enum Pairing Sets Trace Typ Util.

Definition Fair2 {tout} (k : forall {ty1 ty2}, Enum ty1 -> Enum ty2 -> Enum (tout ty1 ty2)) :=
  forall n,
  exists equilibrium,
    match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat)) equilibrium with
      | Tracing l_uses r_uses _ _ =>
        n < equilibrium /\ l_uses ≃ r_uses
    end.

Definition Fair3 {tout} (k : forall {ty1 ty2 ty3}, Enum ty1 -> Enum ty2 -> Enum ty3 -> Enum (tout ty1 ty2 ty3)) :=
  forall n,
  exists equilibrium,
    match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat)) equilibrium with
      | Tracing z_uses o_uses t_uses _ =>
        n < equilibrium /\ z_uses ≃ o_uses /\ o_uses ≃ t_uses
    end.

(* Definition Fair4 (k : Enum -> Enum -> Enum -> Enum -> Enum) := *)
(*   forall n, *)
(*   exists equilibrium, *)
(*     match Trace_lt (k (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat) (E_Trace three E_Nat)) equilibrium with *)
(*       | Tracing z_uses o_uses tw_uses th_uses => *)
(*         n < equilibrium /\ z_uses ≃ o_uses /\ o_uses ≃ tw_uses /\ tw_uses ≃ th_uses *)
(*     end. *)

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
  unfold AltUnfair3, Fair3, not.
  intros [thresh Halt] Hunf.
  destruct (Hunf thresh) as [eq_cand Hblah].
  clear Hunf.
  remember (Halt eq_cand).
  clear Halt Heqy.
  destruct (Trace_lt (k _ _ _ (E_Trace zero E_Nat) (E_Trace one E_Nat) (E_Trace two E_Nat))
                     eq_cand) as [t0 t1 t2 t3] in *.
  intuition.
  assert (t0 ≃ t2) by (eapply set_eq_trans; eauto); contradiction.
Qed.

Section SumFair.
  Lemma Sum_precise
  : forall {tyl tyr} n (e1: Enum tyl) (e2: Enum tyr),
      Trace_lt (E_Sum e1 e2) (double n) ≡ (Trace_lt e1 n) ⊔ (Trace_lt e2 n).
  Proof.
    intros; induction n; [compute; tauto|];
    rewrite double_S; unfold Trace_lt at 1; fold (@Trace_lt (TSum tyl tyr)); unfold Trace_on;
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
  Theorem SumFair : Fair2 (@E_Sum).
  Proof.
    unfold Fair2.
    intros n.
    exists (double (S n)).
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
    apply (@Trace_lt_sub (TSum TNat (TSum TNat TNat)) )with (n := double (double p)); nliamega.
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
      invert_Enumerates; subst;
      destruct (sub_trace_In_equiv (lt ⊔ rt)
                                   ((Trace_lt e1 (S n)) ⊔ (Trace_lt e2 (S n))));
      apply H; [| assumption];
      clear H H0;
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

  Theorem PairFair : Fair2 (@E_Pair).
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
