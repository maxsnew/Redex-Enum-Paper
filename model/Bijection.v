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
  forall {A B} (bi:Bijection A B) b,
    { a | Bijects bi a b }.
Proof.
  intros. exists (biject_from bi b).
  unfold Bijects. intuition.
  unfold biject_from, biject_to.
  destruct bi as [[f g] [F G]].
  simpl in *. auto.
Defined.

Ltac rewrite_biject_funr :=
  match goal with
    | [ H1: Bijects ?b ?x _, H2: Bijects ?b ?x _ |- _ ] =>
      erewrite (Bijects_fun_right _ _ _ _ _ _ H1 H2) in *; clear H1 H2
  end.

(* rewrite_biject_funr tests *)
Goal forall tin tout (b: Bijection tin tout) x v1 v2,
       Bijects b x v1 -> Bijects b x v2 -> v1 = v2.
intros; rewrite_biject_funr; trivial.
Qed.

Goal forall tin tout (b: Bijection tin tout) x v1 v2, Bijects b x v1 -> Bijects b x v2 -> v1 <> v2 -> False.
intros; rewrite_biject_funr; intuition.
Qed.

Section BijExamples.
  Require Import Util.
  Require Import Coq.Arith.Arith_base.
  Definition SwapCons {A B} (p : A * B) :=
    match p with | (x, y) => (y, x) end.
  
  Definition SwapConsBij {A B : Set} : Bijection (A * B) (B * A).
    refine ({{ (SwapCons, SwapCons )}}); split; intros p; destruct p; reflexivity.
  Defined.

  Definition SwapWithZero n m :=
    if eq_nat_dec m 0
    then n
    else if eq_nat_dec m n
         then 0
         else m.
  
  Lemma SwapWithZero_Swaps : forall n a, (SwapWithZero n) ((SwapWithZero n) a) = a.
  Proof.
    intros n n0.
    unfold SwapWithZero.
    destruct (eq_nat_dec n0 0); subst; auto.
    destruct (eq_nat_dec n 0); auto.
    destruct (eq_nat_dec n n); subst; auto.
    intuition.
    destruct (eq_nat_dec n0 n).
    destruct (eq_nat_dec 0 0); subst; auto.
    intuition.
    destruct (eq_nat_dec n0 0); subst; auto.
    intuition.
    destruct (eq_nat_dec n0 n); subst.
    intuition.
    auto.
  Qed.

  Definition SwapWithZeroBijection (n: nat) : Bijection nat nat.
    refine ({{(SwapWithZero n, SwapWithZero n)}}); split; apply SwapWithZero_Swaps.
  Defined.
End BijExamples.
