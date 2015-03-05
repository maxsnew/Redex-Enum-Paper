Require Import Coq.Arith.Arith_base  Coq.Arith.Div2.
Require Import Coq.Lists.ListSet Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import Bijection Pairing Sets Trace Typ Util.

(* Notation notes:
Sets
∅ \emptyset empty_set
∈ \in       set_In
∪ \cup      set_union'
⊂ \subset   subset
≃ \simeq    set_eq

Traces
ε \epsilon  trace_zero
⊔ \sqcup    trace_plus
⊏ \sqsubset sub_trace
≡ \equiv    trace_eq
 *)

Inductive Enum : type -> Set :=
| E_Nat : Enum TNat
| E_Pair {tl tr} : Enum tl -> Enum tr -> Enum (TPair tl tr)
| E_Map {tyin tyout} : Bijection (tdenote tyout) (tdenote tyin) -> Enum tyin -> Enum tyout
| E_Dep {t1 t2} : Enum t1 -> (tdenote t1 -> Enum t2) -> Enum (TPair t1 t2)
| E_Sum {tl tr} : Enum tl -> Enum tr -> Enum (TSum tl tr)
| E_Trace {t} : tag -> Enum t -> Enum t (* A no-op wrapper to signal tracing *)
.
Hint Constructors Enum.

Inductive Enumerates : forall {t : type}, Enum t -> nat -> tdenote t -> Trace -> Prop :=
| ES_Nat :
    forall n,
      Enumerates E_Nat n n ε
| ES_Pair :
    forall {tl tr} (l: Enum tl) (r: Enum tr) n ln rn lx rx lt rt,
      Pairing n ln rn ->
      Enumerates l ln lx lt ->
      Enumerates r rn rx rt ->
      Enumerates (E_Pair l r) n (lx, rx) (lt ⊔ rt)
| ES_Map :
    forall {tl tr} (bi : Bijection (tdenote tl) (tdenote tr)) inner inner_x n x t,
      Bijects bi x inner_x ->
      Enumerates inner n inner_x t ->
      Enumerates (E_Map bi inner) n x t
| ES_Dep:
    forall {tl tr} (l: Enum tl) (f: tdenote tl -> Enum tr) n ln rn lx rx lt rt,
      Pairing n ln rn ->
      Enumerates l ln lx lt ->
      Enumerates (f lx) rn rx rt ->
      Enumerates (E_Dep l f) n (lx, rx) (lt ⊔ rt)
| ES_Sum_Left:
    forall {tl tr} (l: Enum tl) (r: Enum tr) n ln lx t,
      n = 2 * ln ->
      Enumerates l ln lx t ->
      Enumerates (E_Sum l r) n (inl lx) t
| ES_Sum_Right:
    forall {tl tr} (l: Enum tl) (r: Enum tr) n rn rx t,
      n = 2 * rn + 1 ->
      Enumerates r rn rx t ->
      Enumerates (E_Sum l r) n (inr rx) t
(* E_Trace hides traces below it. This makes traces super easily spoofable, but makes it easier to reason about when they're not spoofed *)
| ES_Trace :
    forall {ty} n tg (e: Enum ty) v _t,
      Enumerates e n v _t ->
      Enumerates (E_Trace tg e) n v (trace_one n tg).
Hint Constructors Enumerates.

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

Ltac even_odd_crush :=
  repeat (match goal with
            | [ H: context[double _] |- _] => rewrite double_twice in H
            | [ H: context[S (2 * ?x)] |- _ ] => replace (S (2 * x)) with (2 * x + 1) in * by (nliamega)
            | [ H: 2 * _ = 2 * _ |- _ ] => apply even_fun in H
            | [ H: 2 * _ + 1 = 2 * _ + 1 |- _ ] => apply odd_fun in H
            | [ H: 2 * _     = 2 * _ + 1 |- _] => apply odd_neq_even in H; contradiction
                                                                         | [ H: 2 * _ + 1 = 2 * _     |- _] => symmetry in H; apply odd_neq_even in H; contradiction
          end).

(* if there's a hypothesis of the shape Enumerates ..., inversion; subst; clear it *)
Ltac invert_Enumerates' :=
  match goal with
    | [ H : Enumerates ?E _ _ _ |- _ ] =>
      match E with
        | E_Nat          => inversion H; subst; clear H
        | E_Pair _ _ => inversion H; subst; clear H
        | E_Map _ _  => inversion H; subst; clear H
        | E_Dep _ _  => inversion H; subst; clear H
        | E_Sum _ _  => inversion H; subst; clear H
        | E_Trace _ _  => inversion H; subst; clear H
      end
  end.

Ltac invert_Enumerates := repeat invert_Enumerates'; repeat dec_K.

Ltac odd_neq_event :=
  match goal with
    | [ H : 2 * ?x = 2 * ?y + 1 |- _ ] => apply odd_neq_even in H; contradiction
    | [ H : 2 * ?y + 1 = 2 * ?x |- _ ] => symmetry in H; apply odd_neq_even in H; contradiction
  end.

Ltac Eff_indHyp :=
  match goal with
    | [ IH: context[Enumerates _ _ _ _ -> Enumerates _ _ _ _ -> _ ]
      , H1 : Enumerates ?e _ _ _
      , H2 : Enumerates ?e _ _ _
      |- _ ] => destruct (IH _ _ _ _ _ H1 H2); clear IH H1 H2; subst
  end.

Theorem Enumerates_from_fun :
  forall {ty} (e: Enum ty) n x1 x2 t1 t2,
    Enumerates e n x1 t1 ->
    Enumerates e n x2 t2 ->
    x1 = x2 /\ t1 = t2.
Proof.
  induction e; intros; invert_Enumerates;
  repeat rewrite_pairing_to_fun;
  repeat Eff_indHyp;
  try (even_odd_crush; subst);
  try match goal with
        | [ H1 : Bijects ?b ?x1 ?y, H2 : Bijects ?b ?x2 ?y |- _ ] =>
          erewrite (Bijects_fun_left _ _ _ _ _ _ H1 H2) in *; clear H1 H2
        | [ IH: context[Enumerates _ _ _ _ -> Enumerates _ _ _ _ -> _ /\ _]
          , H1 : Enumerates ?e _ _ _
          , H2 : Enumerates ?e _ _ _
          |- _ ] => destruct (IH _ _ _ _ _ _ H1 H2); clear IH H1 H2; subst
      end;
  repeat Eff_indHyp;
  tauto.
Qed.

Ltac Etf_indHyp :=
  match goal with
    | [ IH: context[Enumerates _ _ _ _ -> Enumerates _ _ _ _ -> _ ]
      , H1 : Enumerates ?e _ _ _
      , H2 : Enumerates ?e _ _ _
      |- _ ] =>
      erewrite (IH _ _ _ _ _ H1 H2) in *; clear IH H1 H2; subst
  end.

Theorem Enumerates_to_fun :
  forall {ty} (e: Enum ty) x n1 n2 t1 t2,
    Enumerates e n1 x t1 ->
    Enumerates e n2 x t2 ->
    n1 = n2.
Proof.
  induction e; intros;
  repeat invert_Enumerates; try sumbool_contra;
  repeat destruct_eq; repeat Etf_indHyp; repeat rewrite_pairing_from_fun; try rewrite_biject_funr;
  try match goal with
        | [ IH: context[Enumerates _ _ _ _ -> Enumerates _ _ _ _ -> _ ]
          , H1 : Enumerates ?e _ _ _
          , H2 : Enumerates ?e _ _ _
          |- _ ] =>
          erewrite (IH _ _ _ _ _ _ H1 H2) in *; clear IH H1 H2; subst
      end;
  repeat Etf_indHyp;
  repeat rewrite_pairing_from_fun;
  tauto.
Qed.

Theorem Enumerates_to_fun'
: forall {ty} (e: Enum ty) x n1 n2 t1 t2,
    Enumerates e n1 x t1 ->
    Enumerates e n2 x t2 ->
    n1 = n2 /\ t1 = t2.
Proof.
  intros; assert (n1 = n2 /\ ((n1 = n2) -> t1 = t2)); [split| tauto];
  [ eapply Enumerates_to_fun; eauto |];
  intros; subst;
  match goal with
    | [H1: Enumerates ?e _ ?x _, H2: Enumerates ?e _ ?x _ |- _ ] =>
      destruct (Enumerates_from_fun _ _ _ _ _ _ H H0); subst
  end; trivial.
Qed.

Ltac Etd_indHyp :=
  match goal with
    | [ H : forall (x0 : ?t), { _ : (prod _ _) | _ }
      , x : ?t
      |- _ ] => destruct (H x) as [[? ?] ?]; clear H
    | [ H : forall (x0 : ?t1) (y0: ?t2), { _ : (prod _ _) | _ }
      , x : ?t1
      , y : ?t2
      |- _ ] => destruct (H x y) as [[? ?] ?]; clear H
  end.    


(* Map/Trace compatibility lemmas *)
Lemma Enumerates_to_dec_Map :
  forall tyin tyout (b: Bijection (tdenote tyin) (tdenote tyout)) e x,
    (forall x, { nt: nat * Trace | let (n, t) := nt in Enumerates e n x t }) ->
    { nt : nat * Trace | let (n, t) := nt in Enumerates (E_Map b e) n x t }.
Proof.
  intros;
  match goal with
    | [ Hb: Bijection ?tout _, Hx: ?tout |- _ ] => destruct (Bijects_to_dec _ _ Hb Hx)
  end;
  Etd_indHyp; eexists (_, _); eauto.
Defined.
Hint Resolve Enumerates_to_dec_Map.

Definition Enumerates_to_dec:
  forall {ty} (e : Enum ty) x,
    { nt : nat * Trace | let (n, t) := nt in Enumerates e n x t }.
Proof.
  induction e; intros; auto;
  try (eexists (_, _); eauto; fail);
  tdenote_crush; repeat Etd_indHyp; (eexists (_, _); eauto).
Defined.

Definition Enumerates_to_dec_uniq :
  forall {ty} (e: Enum ty) x,
    (exists ! (nt : nat * Trace),
       let (n, t) := nt in
       Enumerates e n x t).
Proof.
  intros; destruct (Enumerates_to_dec e x) as [[n t] Henum];
  exists (n, t); split; [assumption|];
  intros [n' t'] Henum'; destruct (Enumerates_to_fun' _ _ _ _ _ _ Henum Henum'); subst; auto.
Qed.

Lemma even_SS :
  forall n,
    { l | n = 2 * l } -> { m | S (S n) = 2 * m }.
Proof.
  intros n P; destruct P; exists ((S x)); nliamega.
Defined.

Lemma odd_SS :
  forall n,
    { r | n = 2 * r + 1 } -> { m | S (S n) = 2 * m + 1 }.
Proof.
  intros n P; destruct P; exists ((S x)); nliamega.
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
  forall {ty} (e: Enum ty) n,
    { xt : tdenote ty * Trace | let (x, t) := xt in Enumerates e n x t }.
Proof.
  refine (fix F {ty} e n : { xt : tdenote ty * Trace | let (x, t) := xt in Enumerates e n x t } :=
            match e with
              | E_Nat  => {{(n, ε)}}
              | E_Pair _ _ el er =>
                match Pairing_from_dec n with
                  | {{ p }} =>
                    match F el (fst p), F er (snd p) with
                      | {{ lxt }}, {{ rxt }} =>
                        {{ ((fst lxt, fst rxt), (snd lxt ⊔ snd rxt)) }}
                    end
                end
              | E_Map _ _ b ein  =>
                match F ein n with
                  | {{ xt }} =>
                    match Bijects_from_dec b (fst xt) with
                      | {{ y }} => {{ (y, snd xt ) }}
                    end
                end
              | E_Dep _ _ e f =>
                match Pairing_from_dec n with
                  | {{ p }} =>
                    match F e (fst p) with
                      | {{ lxt }} =>
                        match F (f (fst lxt)) (snd p) with
                          | {{ rxt }} => {{ ((fst lxt, fst rxt), snd lxt ⊔ snd rxt ) }}
                        end
                    end
                end
              | E_Sum _ _ el er =>
                match even_odd_eq_dec n with
                  | inl {{ l }} =>
                    match F el l with
                      | {{ lxt }} =>
                        {{ (inl (fst lxt), snd lxt) }}
                    end
                  | inr {{ r }} =>
                    match F er r with
                      | {{ rxt }} =>
                        {{ (inr (fst rxt), snd rxt) }}
                    end
                end
              | E_Trace _ tg e =>
                match F e n with
                  | {{ xt }} =>
                    {{ (fst xt, trace_one n tg)}}
                end
            end); clear F; tdenote_crush; eauto.
Defined.

Definition Enumerates_from_dec_uniq :
  forall {ty} (e: Enum ty) n,
  exists ! (xt : tdenote ty * Trace),
    let (x, t) := xt
    in Enumerates e n x t.
Proof.
  intros;
  destruct (Enumerates_from_dec e n) as [[v t] Henum];
  exists (v, t);
  split; [assumption|];
  intros [v' t'] Henum'; destruct (Enumerates_from_fun _ _ _ _ _ _ Henum Henum'); subst; auto.
Qed.  

Ltac Eff :=
  match goal with
    | [H1: Enumerates ?e ?n _ _, H2: Enumerates ?e ?n _ _ |- _ ] =>
      destruct (Enumerates_from_fun _ _ _ _ _ _ H1 H2)
  end.

Definition Trace_on {ty} (e : Enum ty) (n : nat) : Trace :=
  (snd (proj1_sig (Enumerates_from_dec e n))).

Fixpoint Trace_lt {ty} (e : Enum ty) n : Trace :=
  match n with
    | 0 => ε
    | S n' => (Trace_on e n') ⊔ (Trace_lt e n')
  end.

Fixpoint Trace_from_to {ty} (e : Enum ty) lo hi : Trace :=
  if le_lt_dec hi lo
  then ε
  else match hi with
         | 0 => ε
         | S hi' => (Trace_on e hi') ⊔ (Trace_from_to e lo hi')
       end.
  
Theorem trace_lt_from_to_0_same {ty} (e : Enum ty) n : (Trace_lt e n) ≡ (Trace_from_to e 0 n).
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

Theorem trace_from_to_ge {ty} (e:Enum ty) m n
: n <= m ->
  Trace_from_to e m n = ε.
Proof.
  intros H.
  unfold Trace_from_to.
  remember (le_lt_dec n m) as l.
  destruct l; [| apply False_ind; nliamega ].
  destruct n; rewrite <-Heql; reflexivity.
Qed.

Theorem trace_from_to_self {ty} (e: Enum ty) m 
: Trace_from_to e m m = ε.
Proof. apply trace_from_to_ge; nliamega. Qed.

Theorem trace_from_to_split1r {ty} (e:Enum ty) m n
: m <= n ->
  (Trace_from_to e m (S n)) ≡ ((Trace_from_to e m n) ⊔ (Trace_on e n)).
Proof.
  intros H.
  unfold Trace_from_to at 1.
  remember (le_lt_dec (S n) m).
  destruct s.
  assert (S n <= n).
  apply le_trans with (m := m); auto.
  apply le_Sn_n in H0.
  contradiction.
  fold (@Trace_from_to ty).
  apply trace_plus_comm.
Qed.

Theorem trace_from_to_split1l' {ty} (e: Enum ty) m n
: (Trace_from_to e m (S (m + n))) ≡ ((Trace_on e m) ⊔ (Trace_from_to e (S m) (S (m + n)))).
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

  fold (@Trace_from_to ty).
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
  fold (@Trace_from_to ty).
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

Theorem trace_from_to_split1l {ty} (e : Enum ty) m n
: m < n ->
  Trace_from_to e m n ≡ (Trace_on e m) ⊔ (Trace_from_to e (S m) n).
Proof.
  intros H.
  remember (pred (n - m)) as t.
  assert (n = (S (m + t))) by nliamega.
  subst n.
  apply trace_from_to_split1l'.
Qed.

Theorem trace_from_to_split {ty} (e : Enum ty) m n p :
  (m <= n < p)
  -> Trace_from_to e m p ≡ (Trace_from_to e m n) ⊔ (Trace_from_to e n p).
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

  apply trace_eq_trans with ((Trace_from_to e m n) ⊔ (Trace_from_to e n p));
    [apply IHn; nliamega| ].
  apply trace_eq_trans with ((Trace_from_to e m n)
                                 ⊔ ((Trace_on e n) ⊔ (Trace_from_to e (S n) p))).
  apply trace_plus_cong; [apply trace_eq_refl| ].
  apply trace_from_to_split1l; nliamega.

  eapply trace_eq_trans.
  apply trace_plus_assoc.
  apply trace_plus_cong; [| apply trace_eq_refl].
  apply trace_eq_symm.
  apply trace_from_to_split1r; nliamega.
Qed.

Theorem trace_from_to_0_split :
  forall m n {ty} (e : Enum ty),
    m < n ->
    Trace_lt e n ≡ (Trace_lt e m) ⊔ (Trace_from_to e m n).
Proof.
  intros m n ty e Hmn.
  eapply trace_eq_trans.
  apply trace_lt_from_to_0_same.
  eapply trace_eq_trans.
  apply (@trace_from_to_split ty) with (n := m); split; [nliamega | assumption].
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

Theorem trace_off tg1 tg2 n : tg1 <> tg2 -> trace_proj tg2 (Trace_on (E_Trace tg1 E_Nat) n) = ∅.
Proof.
  rewrite Trace_nat.
  compute.
  destruct tg1; destruct tg2; intuition.
Qed.

Theorem trace_proj_plus_distrl tg t1 t2
: trace_proj tg (t1 ⊔ t2) = ((trace_proj tg t1) ∪ (trace_proj tg t2)).
Proof.
  destruct t1; destruct t2; destruct tg; auto.
Qed.

Theorem Trace_on_correct {ty} (e: Enum ty) n x t : Enumerates e n x t -> Trace_on e n = t.
Proof.
  intros H.
  unfold Trace_on.
  destruct (Enumerates_from_dec e n) as [[v tgaf] Henum].
  simpl.
  destruct (Enumerates_from_fun _ _ _ _ _ _ H Henum); auto.
Qed.

Theorem trace_lt_Nat n tg
: z_to_n n ≃ trace_proj tg (Trace_lt (E_Trace tg E_Nat) n).
Proof.
  induction n as [| n IHn]; [destruct tg; compute; tauto|].
  unfold Trace_lt. fold (@Trace_lt TNat).
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
  unfold Trace_lt; fold (@Trace_lt TNat).
  rewrite trace_proj_plus_distrl.
  rewrite trace_off.
  rewrite IHn; compute; auto.
  auto.
Qed.

Lemma sub_trace_from_tol {ty} l m n (e: Enum ty)
: l <= m
  -> (Trace_from_to e m n) ⊏ (Trace_from_to e l n).
Proof.
  intros H; remember (m - l) as k; replace m with (l + k) by nliamega; clear dependent m.
  induction k.
  replace (l + 0) with l by nliamega; apply sub_trace_refl.
  eapply sub_trace_trans; [| apply IHk].
  destruct (le_dec n (l + S k)).
  rewrite trace_from_to_ge by assumption;
    apply sub_trace_zero.
  eapply sub_trace_trans;
    [| apply trace_eq_weakenl; apply trace_eq_symm; apply (@trace_from_to_split ty) with (n := l + S k); nliamega ];
    apply sub_trace_plus_transr; apply sub_trace_refl.
Qed.

Theorem sub_trace_from_to l m n p {ty} (e : Enum ty)
: l <= m
  -> n <= p
  -> (Trace_from_to e m n) ⊏ (Trace_from_to e l p).
Proof.
  intros Hlm Hnp.
  remember (p - n) as k; replace p with (n + k) by nliamega; clear dependent p.
  induction k.
  replace (n+0) with n by nliamega; apply sub_trace_from_tol; auto.
  replace (n + S k) with (S (n + k)) by nliamega.
  unfold Trace_from_to at 2.
  remember (le_lt_dec (S (n + k)) l) as Hlelt.
  destruct Hlelt.
  replace (Trace_from_to e l (n + k)) with ε in IHk; auto.
  symmetry.
  apply trace_from_to_ge; nliamega.
  fold (@Trace_from_to ty).
  apply sub_trace_plus_transr; auto.
Qed.

Theorem trace_from_to_Nat_off m n tg1 tg2
: tg1 <> tg2 ->
  (trace_proj tg1 (Trace_from_to (E_Trace tg2 E_Nat) m n)) = ∅.
Proof.
  intros Hdiff.
  assert ((Trace_from_to (E_Trace tg2 E_Nat) m n) ⊏ (Trace_lt (E_Trace tg2 E_Nat) n)).
  eapply sub_trace_trans.
  apply sub_trace_from_to with (l := 0) (p := n); try nliamega.
  apply trace_eq_weakenl; apply trace_eq_symm; apply trace_lt_from_to_0_same.
  apply subset_nil_nil.
  erewrite <-trace_lt_Nat_off; [ apply sub_trace_proj|]; eauto.
Qed.

Ltac get_trace_ons :=
  repeat (match goal with
     | [ H: Enumerates _ _ _ _ |- _] => apply Trace_on_correct in H
   end).
  
Theorem trace_on_Pair_off {tyl tyr} tg (e1 : Enum tyl) (e2: Enum tyr) m
: (forall n, trace_proj tg (Trace_on e1 n) = ∅)
  -> (forall n, trace_proj tg (Trace_on e2 n) = ∅)
  -> trace_proj tg (Trace_on (E_Pair e1 e2) m) = ∅.
Proof.
  intros; unfold Trace_on; destruct (Enumerates_from_dec _ _) as [[v t] Henum]; simpl;
  invert_Enumerates;
  get_trace_ons; subst;
  rewrite trace_proj_plus_distrl;
  repeat (match goal with
     | [H1: forall (x: ?t), _ = _,
        x: ?t
       |- _] => rewrite H1 in *
   end); trivial.
Qed.

Theorem trace_lt_Pair_off {tyl tyr} tg (e1 : Enum tyl) (e2 : Enum tyr) m
: (forall n, trace_proj tg (Trace_on e1 n) = ∅)
  -> (forall n, trace_proj tg (Trace_on e2 n) = ∅)
  -> trace_proj tg (Trace_lt (E_Pair e1 e2) m) = ∅.
Proof.
  induction m; [intros; destruct tg; reflexivity|].
  intros H1 H2.
  unfold Trace_lt; fold (@Trace_lt (TPair tyl tyr)).
  rewrite trace_proj_plus_distrl.
  apply subset_nil_nil.
  apply subset_union_both.
  rewrite trace_on_Pair_off; [apply subset_refl| |]; auto.
  rewrite IHm; auto.
Qed.

Theorem trace_on_Sum_off {tyl tyr} tg (e1 : Enum tyl) (e2 : Enum tyr) m
: (forall n, trace_proj tg (Trace_on e1 n) = ∅)
  -> (forall n, trace_proj tg (Trace_on e2 n) = ∅)
  -> trace_proj tg (Trace_on (E_Sum e1 e2) m) = ∅.
Proof.
  intros Hl Hr; unfold Trace_on;
  remember (Enumerates_from_dec (E_Sum e1 e2) m) as x eqn:Heqx; clear Heqx; destruct x as [[v t] Henum]; simpl;
  invert_Enumerates; get_trace_ons; subst; auto.
Qed.

Theorem trace_lt_Sum_off {tyl tyr} tg (e1 : Enum tyl) (e2 : Enum tyr) m
: (forall n, trace_proj tg (Trace_on e1 n) = ∅)
  -> (forall n, trace_proj tg (Trace_on e2 n) = ∅)
  -> trace_proj tg (Trace_lt (E_Sum e1 e2) m) = ∅.
Proof.
  induction m; [intros; compute; destruct tg; trivial|];
  intros; unfold Trace_lt; (fold (@Trace_lt (TSum tyl tyr))); rewrite trace_proj_plus_distrl;
  rewrite IHm; auto; apply trace_on_Sum_off; auto.
Qed.

Theorem set_In_trace' {ty} tg (e : Enum ty) x m n :
  x ∈ (trace_proj tg (Trace_from_to e m (S (m + n))))
  <->
  (exists k,
     m <= k < S (m + n) /\ x ∈ (trace_proj tg (Trace_on e k))).
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
                      fold (@Trace_from_to ty) in H;
                        rewrite trace_from_to_self in H;
                        remember ((Trace_on e m) ⊔ ε) as t;
                        destruct t;
                        simpl in *;
                        remember (Trace_on e m) as t';
                        destruct t';
                        simpl in *;
                        inversion Heqt; subst; auto ])
  | unfold Trace_from_to; fold (@Trace_from_to ty);
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
    fold (@Trace_from_to ty); rewrite trace_from_to_self; assert (k = m) by nliamega; subst;

    remember ((Trace_on e m) ⊔ ε) as t;
    destruct t; simpl in *;
    remember (Trace_on e m) as t';
    destruct t';
    simpl in *;
    inversion Heqt; subst; auto.

  replace (S (m + n)) with (m + S n) in * by nliamega;
    destruct (eq_nat_dec k (m + S n)); subst;
    unfold Trace_from_to; fold (@Trace_from_to ty);
    (destruct (le_lt_dec (S (m + S n)) m); [ assert (~ (S (m + S n) <= m)) by (apply le_not_gt; nliamega); contradiction| ]); (remember (Trace_on e (m + S n)) as t); destruct t as [t0 t1 t2 t3];
    (remember (Trace_from_to e m (m + S n)) as t'); destruct t' as [t0' t1' t2' t3'].
  destruct tg; (
      simpl in *; apply set_union_intro1; auto).

  destruct tg; simpl in *; apply set_union_intro2; apply IHn; nliamega.
Qed.

Theorem set_In_Trace_from_to {ty} (tg : tag) (e: Enum ty) x m n :
  (m < n) ->
  (x ∈ (trace_proj tg (Trace_from_to e m n)) <->
   (exists k, m <= k < n /\ x ∈ (trace_proj tg (Trace_on e k)))).
Proof.
  intros H; remember (pred (n - m)) as p; replace n with (S (m + p)) in * by nliamega; clear n;
  apply set_In_trace'.
Qed.

Theorem set_In_Trace_lt {ty} tg (e: Enum ty) x n :
  x ∈ (trace_proj tg (Trace_lt e (S n)))
  <->
  exists k, k < S n /\ x ∈ (trace_proj tg (Trace_on e k)).
Proof.
  destruct (set_In_Trace_from_to tg e x 0 (S n)) as [Hl Hr]; try nliamega.
  split; [clear Hr|clear Hl].
  intros Hin.
  assert (x ∈ (trace_proj tg (Trace_from_to e 0 (S n)))).
  apply In_subset_def with (trace_proj tg (Trace_lt e (S n))); [| assumption].
  apply sub_trace_proj; apply trace_eq_weakenl; apply trace_lt_from_to_0_same.
  destruct (Hl H) as [k [? Hink]].
  exists k; split; [nliamega| assumption].
  
  intros Hex; destruct Hex as [k [Hbound Hink]].
  assert (x ∈ (trace_proj tg (Trace_from_to e 0 (S n)))).
  apply Hr.
  exists k; split; [nliamega| assumption].
  apply In_subset_def with (trace_proj tg (Trace_from_to e 0 (S n))); [| assumption].
  apply sub_trace_proj; apply trace_eq_weakenr; apply trace_lt_from_to_0_same.
Qed.

Theorem sub_trace_plus_introl t1 t2 t3
: t1 ⊏ t2 -> t1 ⊏ (t2 ⊔ t3).
Proof.
  unfold sub_trace, trace_plus; destruct t1, t2, t3.
  intros H; destruct H as [H1 [H2 [H3 H4]]].
  Local Hint Resolve subset_union_transl.
  split4; auto.
Qed.

Theorem sub_trace_plus_intror t1 t2 t3
: t1 ⊏ t3 -> t1 ⊏ (t2 ⊔ t3).
Proof.
  unfold sub_trace, trace_plus; destruct t1, t2, t3.
  intros H; destruct H as [H1 [H2 [H3 H4]]].
  Local Hint Resolve subset_union_transr.
  split4; auto.
Qed.

Theorem Trace_from_to_sub' {ty} (e : Enum ty) m n p : (Trace_from_to e m n) ⊏ (Trace_from_to e m (n + p)).
Proof.
  induction p.
  replace (n + 0) with n by nliamega; apply sub_trace_refl.
  replace (n + S p) with (S (n + p)) by nliamega.
  unfold Trace_from_to at 2; fold (@Trace_from_to ty).
  destruct (le_lt_dec (S (n + p))).
  replace (Trace_from_to e m n) with ε; [apply sub_trace_refl|].
  unfold Trace_from_to.
  destruct n.
  destruct (le_lt_dec 0 m); auto.
  destruct (le_lt_dec (S n) m); auto; nliamega.
  apply sub_trace_plus_intror; auto.
Qed.

Theorem Trace_from_to_sub {ty} (e: Enum ty) m n p : n <= p -> (Trace_from_to e m n) ⊏ (Trace_from_to e m p).
Proof.
  Local Hint Resolve Trace_from_to_sub'.
  intros; replace p with (n + (p - n)) by nliamega; auto.
Qed.

Theorem Trace_lt_sub {ty} (e: Enum ty) m n : m <= n -> (Trace_lt e m) ⊏ (Trace_lt e n).
Proof.
  intros H.
  eapply sub_trace_trans; [apply trace_eq_weakenl; apply trace_lt_from_to_0_same| ].
  eapply sub_trace_trans; [| apply trace_eq_weakenr; apply trace_lt_from_to_0_same].
  apply Trace_from_to_sub; auto.
Qed.

Theorem Trace_lt_Enumerates m n {ty} (e: Enum ty) v t 
: m < n
  -> Enumerates e m v t
  -> t ⊏ (Trace_lt e n).
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
