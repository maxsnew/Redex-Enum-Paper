Require Import Util.
Inductive type : Set :=
| TNat  : type
| TPair : type -> type -> type
| TSum  : type -> type -> type.

Fixpoint type_eq_dec (t1 t2 : type) : { t1 = t2 } + { t1 <> t2 }.
refine (match t1, t2 with
          | TNat, TNat => Yes
          | TPair t1l t1r, TPair t2l t2r =>
            (type_eq_dec t1l t2l) &&& Refine (type_eq_dec t1r t2r)
          | TSum t1l t1r, TSum t2l t2r =>
            (type_eq_dec t1l t2l) &&& Refine (type_eq_dec t1r t2r)
          | _, _ => right _
        end
       ); subst; try discriminate; try congruence; auto.
Defined.

Fixpoint tdenote t : Set :=
  match t with
    | TNat => nat
    | TPair tl tr => tdenote tl * tdenote tr
    | TSum  tl tr => tdenote tl + tdenote tr
  end%type.
Hint Resolve type_eq_dec.
Ltac tdenote_crush :=
  repeat (
      match goal with
        | [ x : prod ?t1 ?t2 |- _] => destruct x
        | [ x : sum ?t1 ?t2 |- _] => destruct x
        | [ H : tdenote ?t |- _ ] =>
          match t with
            | TNat      => simpl in H
            | TPair _ _ => simpl in H
            | TSum _ _  => simpl in H
          end
      end).
