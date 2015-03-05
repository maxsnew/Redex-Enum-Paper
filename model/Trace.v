Require Import Sets Util.

Inductive Trace :=
| Tracing : set' -> set' -> set' -> set' -> Trace.

Inductive tag : Set :=
| zero  : tag
| one   : tag
| two   : tag
| three : tag.

Definition trace_proj tg t :=
  match t with
    | Tracing t0 t1 t2 t3 =>
      match tg with
        | zero  => t0
        | one   => t1
        | two   => t2
        | three => t3
      end
  end.

Definition trace_zero : Trace := Tracing ∅ ∅ ∅ ∅.
                                         Notation ε := trace_zero.
Definition trace_plus (t1 t2 : Trace) : Trace :=
  match (t1, t2) with
    | (Tracing l1 l2 l3 l4, Tracing r1 r2 r3 r4) =>
      Tracing (l1 ∪ r1) (l2 ∪ r2) (l3 ∪ r3) (l4 ∪ r4)
  end.
Notation "x ⊔ y" := (trace_plus x y) (at level 50).

Definition trace_one n t : Trace :=
  match t with
    | zero  => Tracing (set_add' n ∅) ∅ ∅ ∅
    | one   => Tracing ∅ (set_add' n ∅) ∅ ∅
    | two   => Tracing ∅ ∅ (set_add' n ∅) ∅
    | three => Tracing ∅ ∅ ∅ (set_add' n ∅)
  end.

Definition trace_eq (t1 t2 : Trace) : Prop :=
  match (t1, t2) with
    | (Tracing l0 l1 l2 l3, Tracing r0 r1 r2 r3) =>
      l0 ≃ r0 /\ l1 ≃ r1 /\ l2 ≃ r2 /\ l3 ≃ r3
  end.
Notation "t1 ≡ t2" := (trace_eq t1 t2) (at level 70, no associativity).

Definition sub_trace (t1 t2 : Trace) : Prop :=
  match (t1, t2) with
    | (Tracing l0 l1 l2 l3, Tracing r0 r1 r2 r3) =>
      l0 ⊂ r0 /\ l1 ⊂ r1 /\ l2 ⊂ r2 /\ l3 ⊂ r3
  end.
Notation "t1 ⊏ t2" := (sub_trace t1 t2) (at level 70, no associativity).

Theorem sub_trace_refl t : t ⊏ t.
Proof.
  unfold sub_trace; destruct t; split4; apply subset_refl.
Qed.
Hint Resolve sub_trace_refl.

Theorem sub_trace_trans t1 t2 t3 : t1 ⊏ t2 -> t2 ⊏ t3 -> t1 ⊏ t3.
Proof.
  unfold sub_trace; destruct t1, t2, t3.
  intros H1 H2; destruct4 H1; destruct4 H2.
  split4; eapply subset_trans; eauto.
Qed.

Theorem sub_trace_zero t : ε ⊏ t.
Proof. destruct t; compute; tauto. Qed.

Theorem trace_eq_proj t1 t2 tg : t1 ≡ t2 -> (trace_proj tg t1) ≃ (trace_proj tg t2).
Proof.
  unfold trace_eq, trace_proj; destruct t1; destruct t2; destruct tg; intuition.
Qed.

Theorem sub_trace_proj t1 t2 tg : t1 ⊏ t2 -> (trace_proj tg t1) ⊂ (trace_proj tg t2).
Proof.
  unfold sub_trace; destruct t1; destruct t2; destruct tg; intuition.
Qed.

Definition trace_eq' t1 t2 : Prop :=
  t1 ⊏ t2 /\ t2 ⊏ t1.
Theorem trace_eq'_weakenl t1 t2 : trace_eq' t1 t2 -> t1 ⊏ t2.
Proof. unfold trace_eq'; intuition. Qed.
Theorem trace_eq'_weakenr t1 t2 : trace_eq' t1 t2 -> t2 ⊏ t1.
Proof. unfold trace_eq'; intuition. Qed.
Theorem trace_eq_eq'_equiv t1 t2 : t1 ≡ t2 <-> trace_eq' t1 t2.
Proof.
  unfold trace_eq, trace_eq', sub_trace, set_eq;
  destruct t1; destruct t2; intuition.
Qed.

Theorem trace_eq_weakenl t1 t2 : t1 ≡ t2 -> t1 ⊏ t2.
Proof. rewrite trace_eq_eq'_equiv; apply trace_eq'_weakenl. Qed.

Theorem trace_eq_weakenr t1 t2 : t1 ≡ t2 -> t2 ⊏ t1.
Proof. rewrite trace_eq_eq'_equiv; apply trace_eq'_weakenr. Qed.

Theorem trace_plus_cong t1 t2 t3 t4 : t1 ≡ t3 -> t2 ≡ t4 -> (t1 ⊔ t2) ≡ (t3 ⊔ t4).
  unfold trace_eq.
  destruct t1; destruct t2; destruct t3; destruct t4.
  unfold trace_plus.
  intros H; destruct4 H.
  intros H'; destruct4 H'.
  split4; apply set_union_cong; auto.
Qed.

Theorem trace_eq_refl t : t ≡ t.
Proof.
  unfold trace_eq; destruct t; split4; apply set_eq_refl.
Qed.
Hint Resolve trace_eq_refl.

Theorem trace_eq_symm t1 t2 : t1 ≡ t2 -> t2 ≡ t1.
Proof.
  unfold trace_eq.
  destruct t1; destruct t2.
  intros H; destruct4 H.
  split4; apply set_eq_symm; auto.
Qed.

Theorem trace_eq_trans t1 t2 t3 : t1 ≡ t2 -> t2 ≡ t3 -> t1 ≡ t3.
Proof.
  unfold trace_eq.
  destruct t1; destruct t2; destruct t3.
  intros H; destruct4 H.
  intros H'; destruct4 H'.
  split4; eapply set_eq_trans; eauto.
Qed.

Theorem trace_plus_comm t1 t2 : (t1 ⊔ t2) ≡ (t2 ⊔ t1).
Proof.
  destruct t1, t2.
  unfold trace_plus.
  split4; apply set_eq_union_comm.
Qed.

Theorem trace_plus_assoc t1 t2 t3 : (t1 ⊔ (t2 ⊔ t3)) ≡ ((t1 ⊔ t2) ⊔ t3).
Proof.
  destruct t1, t2, t3.
  unfold trace_plus.
  split4; apply set_eq_symm; apply set_union_assoc.
Qed.

Theorem sub_trace_plus_transl t tl tr
: t ⊏ tl -> t ⊏ (tl ⊔ tr).
Proof.
  intros H; destruct t; destruct tl; destruct tr;
  destruct4 H; split4; apply subset_union_transl; auto.
Qed.

Theorem sub_trace_plus_transr t tl tr
: t ⊏ tr -> t ⊏ (tl ⊔ tr).
Proof.
  intros H.
  eapply sub_trace_trans.
  Focus 2.
  apply trace_eq_weakenl.
  apply trace_plus_comm.
  apply sub_trace_plus_transl; auto.
Qed.

Theorem sub_trace_plus_eq : forall t1 t2, t1 ⊏ t2 -> (t1 ⊔ t2) ≡ t2.
Proof.
  intros t1 t2 H; destruct t1; destruct t2;
  destruct4 H; split4; apply subset_union_eq; auto.
Qed.

Theorem trace_plus_unitl t : (ε ⊔ t) ≡ t.
Proof.
  destruct t; split4; apply set_union_unitl.
Qed.

Theorem trace_plus_unitl_gen t1 t2 : t1 ≡ t2 -> (ε ⊔ t1) ≡ t2.
Proof.
  intros H.
  eapply trace_eq_trans; [ apply trace_plus_unitl | auto].
Qed.


Theorem trace_plus_unitr t :
  (t ⊔ ε) ≡ t.
Proof.
  eapply trace_eq_trans;
  [apply trace_plus_comm| apply trace_plus_unitl].
Qed.


Theorem trace_plus_unitr_gen t1 t2 : t1 ≡ t2 -> (t1 ⊔ ε) ≡ t2.
Proof.
  intros H.
  eapply trace_eq_trans; [ apply trace_plus_unitr | auto].
Qed.

Theorem sub_trace_plus_cong tl1 tr1 tl2 tr2 : 
  tl1 ⊏ tl2
  -> tr1 ⊏ tr2
  -> (tl1 ⊔ tr1) ⊏ (tl2 ⊔ tr2).
Proof.
  unfold sub_trace, trace_plus.
  destruct tl1; destruct tl2; destruct tr1; destruct tr2.
  intros Hl; destruct4 Hl.
  intros Hr; destruct4 Hr.
  split4; apply set_union_subset_cong; auto.
Qed.

Theorem trace_proj_reconstruct t 
: t = Tracing (trace_proj zero t) (trace_proj one t) (trace_proj two t) (trace_proj three t).
Proof.
  destruct t; reflexivity.
Qed.

Theorem sub_trace_In_equiv t1 t2
: t1 ⊏ t2 
  <-> 
  (forall x tg, x ∈ (trace_proj tg t1) -> x ∈ (trace_proj tg t2)).
Proof.
  destruct t1; destruct t2; split.
  intros Hst x tg Hin; destruct4 Hst; destruct tg; eapply subset_In; eassumption.
  intros H; rewrite trace_proj_reconstruct; rewrite trace_proj_reconstruct at 1;
  split4; apply subset_In_def; intros; apply H; assumption.
Qed.

Theorem sub_trace_In_util t1 t2 x tg
: t1 ⊏ t2 
  -> x ∈ (trace_proj tg t1)
  -> x ∈ (trace_proj tg t2).
Proof.
  intros Hsub.
  generalize x tg.
  generalize Hsub.
  apply sub_trace_In_equiv.
Qed.
