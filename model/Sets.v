Require Import Coq.Arith.Arith_base.
Require Import Coq.Lists.ListSet Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import Util.

Notation set' := (set nat).
Notation "∅" := (@empty_set nat).
Notation "p ∪ q" := (@set_union nat eq_nat_dec p q) (at level 50).
Notation set_add' := (@set_add nat eq_nat_dec).
Notation "x ∈ s" := (set_In x s) (at level 70).

Fixpoint subset (s1 s2 : set nat) :=
  match s1 with
    | nil => True
    | x :: more =>
      x ∈ s2 /\ subset more s2
  end.
Hint Unfold subset.
Notation "s1 ⊂ s2" := (subset s1 s2) (at level 70, no associativity).

Theorem subset_nil : forall s, nil ⊂ s.
Proof.
  auto.
Qed.

Theorem subset_nil_nil : forall s, s ⊂ nil -> s = nil.
Proof.
  induction s.
  auto.
  intros contra.
  unfold subset in contra.
  destruct contra.
  inversion H.
Qed.

Definition set_eq s1 s2 := s1 ⊂ s2 /\ s2 ⊂ s1.
Hint Unfold set_eq.
Notation "s1 ≃ s2" := (set_eq s1 s2) (at level 70, no associativity).

Lemma subset_consr s1 s2 n : s1 ⊂ s2 -> s1 ⊂ (cons n s2).
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

Definition subset_dec s1 s2 : { s1 ⊂ s2 } + { ~ (s1 ⊂ s2) }.
Proof.
  generalize dependent s2.
  induction s1.
  left; auto.

  intros s2.
  destruct (In_dec eq_nat_dec a s2).

  destruct (IHs1 s2).
  left; constructor; auto.

  right.
  unfold subset; fold subset.
  intros H; destruct H; contradiction.

  right.
  intros H; destruct H; contradiction.
Defined.

Definition subset_nn s1 s2 : ~~(s1 ⊂ s2) -> s1 ⊂ s2.
Proof.
  destruct (subset_dec s1 s2); tauto.
Qed.

Definition set_eq_dec s1 s2 : { s1 ≃ s2 } + { ~ (s1 ≃ s2) }.
Proof.
  destruct (subset_dec s1 s2).
  destruct (subset_dec s2 s1).
  left; auto.
  right; intros contra; destruct contra; apply n; auto.
  right; intros contra; destruct contra; apply n; auto.
Qed.

Theorem subset_refl s : s ⊂ s.
Proof.
  induction s; unfold subset; auto.
  fold subset.
  split.
  constructor 1; auto.
  apply subset_consr; auto.
Qed.
Hint Resolve subset_refl.

Theorem set_eq_refl s : s ≃ s.
Proof.
  split; apply subset_refl.
Qed.
Hint Resolve set_eq_refl.

Theorem subset_In : forall x s s', x ∈ s -> s ⊂ s' -> x ∈ s'.
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

Theorem subset_In_def s s' : (forall x, x ∈ s -> x ∈ s') -> s ⊂ s'.
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

Theorem In_subset_def s s' : s ⊂ s' -> (forall x, x ∈ s -> x ∈ s').
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

Hint Resolve subset_In_def In_subset_def.
Theorem subset_In_equiv s s' : s ⊂ s' <-> (forall x, x ∈ s -> x ∈ s').
Proof.
  split; eauto.
Qed.

Lemma set_subset_weaken : forall s1 s2, s1 ≃ s2 -> s1 ⊂ s2.
Proof.
  unfold set_eq.
  tauto.
Qed.

Theorem not_subset_In_def s s' x : x ∈ s -> ~(x ∈ s') -> ~ s ⊂ s'.
Proof.
  intros; eauto.
Qed.

Lemma subset_trans : forall s1 s2 s3, s1 ⊂ s2 -> s2 ⊂ s3 -> s1 ⊂ s3.
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


Lemma set_eq_trans : forall s1 s2 s3, s1 ≃ s2 -> s2 ≃ s3 -> s1 ≃ s3.
Proof.
  unfold set_eq.
  intros s1 s2 s3 H1 H2; destruct H1; destruct H2.
  split; eapply subset_trans; eauto.
Qed.

Lemma set_eq_symm : forall s1 s2, s1 ≃ s2 -> s2 ≃ s1.
Proof.
  intros s1 s2 H; inversion H; split; auto.
Qed.

(* Theorem set_union_or : forall s1 s2, s1 ⊂ (s1 ∪ s2). *)

Lemma set_add_subset : forall x s1 s2, x ∈ s2 -> s1 ⊂ s2 -> (set_add' x s1) ⊂ s2.
Proof.

  intros y s1.
  induction s1 as [| x s1].
  simpl; auto.
  intros s2 Hy2 Hsub.
  unfold set_add.
  destruct (eq_nat_dec y x); subst; auto.
  fold set_add.
  unfold subset.
  split; auto.
  destruct Hsub; auto.
  fold subset.
  apply IHs1; auto.
  destruct Hsub; auto.
Qed.

Lemma subset_cons_swap : forall x y s1 s2, s1 ⊂ s2 -> (x :: y :: s1) ⊂ (y :: x :: s2).
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

Lemma set_eq_cons_swap : forall x y s1 s2, s1 ≃ s2 -> (x :: y :: s1) ≃ (y :: x :: s2).
Proof.
  split; destruct H; apply subset_cons_swap; auto.
Qed.

Lemma set_cons_cons_subset : forall x s1 s2, s1 ⊂ s2 -> (x :: s1) ⊂ (x :: s2).
Proof.
  intros x s1 s2 Hsub.
  unfold subset. fold subset.
  split.
  constructor; auto.
  apply subset_consr; auto.
Qed.

Lemma set_eq_cons_cons x s1 s2 : s1 ≃ s2 -> (x :: s1) ≃ (x :: s2).
Proof.
  intros H.
  destruct H.
  split; apply set_cons_cons_subset; auto.
Qed.

Lemma set_add_cons_eq : forall x s, (x :: s) ≃ (set_add' x s).
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

Lemma set_add_cons_subset : forall x s1 s2, s1 ⊂ s2 -> (x :: s1) ⊂ (set_add' x s2).
Proof.
  intros x s1 s2 Hsub.
  apply subset_trans with (s2 := (x :: s2)).
  apply set_cons_cons_subset; auto.
  apply set_subset_weaken.
  apply set_add_cons_eq.
Qed.

Lemma set_union_unitl : forall s, (∅ ∪ s) ≃ s.
Proof.
  split.
  induction s.
  apply subset_refl.

  unfold set_union in *.
  replace (((fix set_union (x y : set nat) {struct y} :
               set nat :=
               match y with
                 | nil => x
                 | a1 :: y1 => set_add eq_nat_dec a1 (set_union x y1)
               end) ∅ s
           )) with (∅ ∪ s) in * by auto.
  apply set_add_subset; auto.
  constructor; auto.
  apply subset_consr; auto.

  induction s; auto.
  unfold set_union.
  apply set_add_cons_subset; auto.
Qed.

Lemma set_union_unitr : forall s, (s ∪ ∅) ≃ s.
Proof.
  apply set_eq_refl.
Qed.

Lemma elem_union :
  forall s x,
    x ∈ s -> forall s', x ∈ (s' ∪ s).
Proof.
  induction s.
  intros H contra.
  inversion contra.

  intros x Hin s'.
  simpl.
  assert (x ∈ (a :: (s' ∪ s))).
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

Lemma subset_union_cons : forall x s1 s2, ((x::s1) ∪ s2) ⊂ (x :: (s1 ∪ s2)).
  induction s2.
  simpl; split.
  tauto.
  apply subset_consr; apply subset_refl.
  simpl.
  eapply subset_trans.
  apply set_add_cons_eq.
  apply subset_trans with (s2 := (x :: a :: (s1 ∪ s2))).
  eapply subset_trans.
  apply set_cons_cons_subset.
  apply IHs2.
  apply subset_cons_swap.
  apply subset_refl.
  apply set_cons_cons_subset.
  apply set_add_cons_eq.
Qed.

Theorem subset_union_comm : forall s1 s2, (s1 ∪ s2) ⊂ (s2 ∪ s1).
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

Theorem set_eq_union_comm : forall s1 s2, (s1 ∪ s2) ≃ (s2 ∪ s1).
Proof.
  intros s1 s2.
  split; apply subset_union_comm.
Qed.

Lemma subset_union_transr :
  forall s sl sr,
    s ⊂ sr ->
    s ⊂ (sl ∪ sr).
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
    s ⊂ sl ->
    s ⊂ (sl ∪ sr).
Proof.
  intros.
  eapply subset_trans; [| apply subset_union_comm ].
  apply subset_union_transr; auto.
Qed.


Lemma set_union_subset_cong :
  forall sl sr sl' sr',
    sl ⊂ sl' -> sr ⊂ sr' -> (sl ∪ sr) ⊂ (sl' ∪ sr').
Proof.
  induction sr.
  intros.
  apply subset_trans with (s2 := sl).
  apply set_union_unitr.
  apply subset_union_transl; auto.

  intros sl' sr' Hsubl Hsubr.
  simpl.
  apply subset_trans with (s2 := (a :: sl ∪ sr)).
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
                         sl ≃ sl' -> sr ≃ sr' -> (sl ∪ sr) ≃ (sl' ∪ sr').
Proof.
  intros sl sr sl' sr' Hl Hr.
  destruct Hl as [Hl Hl'].
  destruct Hr as [Hr Hr'].
  split; apply set_union_subset_cong; auto.
Qed.


Lemma set_subset_add : forall x s1 s2, s1 ⊂ s2 -> s1 ⊂ (set_add' x s2).
Proof.
  intros x s1 s2 Hsub.
  eapply subset_trans; [| apply set_add_cons_subset; apply subset_refl ].
  apply subset_consr; auto.
Qed.

Theorem set_eq_app_cons_comm s1 s2 a : (a :: (s1 ++ s2)) ≃ (s1 ++ a :: s2).
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

Theorem set_union_app_eq : forall s1 s2, (s1 ∪ s2) ≃ (s1 ++ s2).
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
                                 s1 ≃ s3 ->
                                 s2 ≃ s4 ->
                                 (s1 ∪ s2) ≃ (s3 ++ s4).
Proof.
  intros s1 s2 s3 s4 H13 H24.
  eapply set_eq_trans; [| apply set_union_app_eq].
  apply set_union_cong; auto.
Qed.


Theorem subset_union_both s sl sr
: sl ⊂ s -> sr ⊂ s -> (sl ∪ sr) ⊂ s.
Proof.
  intros Hls Hrs.
  apply subset_In_def.
  intros x Hin.
  destruct (set_union_elim eq_nat_dec x sl sr).
  apply Hin.
  apply In_subset_def with sl; auto.
  apply In_subset_def with sr; auto.
Qed.

Theorem subset_union_eq : forall s1 s2, s1 ⊂ s2 -> (s1 ∪ s2) ≃ s2.
Proof.
  split; [| apply subset_union_transr; apply subset_refl ].
  generalize dependent s2.
  induction s1 as [| x s1].
  intros s1 Hsubnil.
  apply subset_trans with (s2 := s1).
  apply set_union_unitl; apply subset_refl.
  apply subset_refl.

  intros s2 Hsub.
  apply subset_trans with (s2 := x :: (s1 ∪ s2)).
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
: ((s1 ∪ s2) ∪ s3) ≃ (s1 ∪ (s2 ∪ s3)).
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

Example set_eq_test : ((set_add' 1 (set_add' 0 ∅)) ≃ (set_add' 0 (set_add' 1 ∅))).
Proof.
  compute.
  tauto.
Qed.

Lemma subset_app : forall s1 s2 s3, s1 ⊂ s2 -> s1 ⊂ (s2 ++ s3).
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
Lemma subset_rev : forall s, s ⊂ (rev s).
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

Lemma set_eq_rev : forall s, s ≃ (rev s).
Proof.
  split; try apply subset_rev.
  rewrite <-rev_involutive.
  apply subset_rev.
Qed.

Fixpoint z_to_n n : set nat :=
  match n with
    | 0 => ∅
    | S n' => set_add' n' (z_to_n n')
  end.

Definition n_to_z n : set nat := rev (z_to_n n).

Theorem z_to_n_correct n x
: x ∈ (z_to_n n) <-> x < n.
Proof.
  generalize dependent x.
  induction n.

  intros x; compute; split; [apply False_ind | intros contra; inversion contra].
  intros x.
  destruct (eq_nat_dec x n).
  simpl.
  subst.
  split; [nliamega|].
  intros _.
  apply set_add_intro2; auto.

  split.
  simpl.
  intros H.
  assert (x ∈ (z_to_n n)).
  apply set_add_elim2 with (b := n) (Aeq_dec := eq_nat_dec); auto.
  assert (x < n).
  apply IHn.
  auto.
  nliamega.

  intros H.
  simpl.
  apply set_add_intro1.
  apply IHn.
  nliamega.
Qed.

Lemma z_to_n_nosubS m : ~ (z_to_n (S m)) ⊂ (z_to_n m).
Proof.
  intros H.
  assert (m ∈ (z_to_n m)).
  eapply In_subset_def; eauto.
  apply z_to_n_correct; nliamega.
  rewrite z_to_n_correct in H0.
  nliamega.
Qed.

Lemma z_to_n_nosub' m n : ~ (z_to_n (S (m + n))) ⊂ (z_to_n m).
Proof.
  induction n.
  replace (m + 0) with m by nliamega.
  apply z_to_n_nosubS.
  unfold z_to_n; fold z_to_n.
  replace (m + S n) with (S (m + n)) by nliamega.
  intros H.
  apply IHn.
  apply subset_In_def.
  intros x.
  rewrite z_to_n_correct.
  intros Hlt.
  assert (x ∈ (set_add' (S (m + n)) (z_to_n (S (m + n))))).
  replace (set_add' (S (m + n)) (z_to_n (S (m + n)))) with (z_to_n (S (S (m + n)))).
  apply z_to_n_correct; nliamega.
  trivial.
  eapply In_subset_def.
  apply H.
  auto.
Qed.

Lemma z_to_n_nosub m n : m < n -> ~ (z_to_n n) ⊂ (z_to_n m).
Proof.
  intros H1 H2.
  destruct n; [nliamega|].
  assert (n < m); [| nliamega].
  apply z_to_n_correct.
  eapply In_subset_def.
  eapply subset_trans; eauto.
  unfold set_In.
  rewrite !z_to_n_correct; auto.
Qed.
