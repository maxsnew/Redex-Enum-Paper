Require Import Enum.
Require Import String.
Open Scope string_scope.

Fixpoint show_all' (e : Enum) (hi : nat) : list Value * Trace.
  refine (match hi with
            | 0 => (nil, trace_zero)
            | S hi' => _
          end).
  destruct (show_all' e hi') as [lold told].
  destruct (Enumerates_from_dec e hi') as [[v t] _].
  exact (cons v lold, trace_plus t told).
Defined.
Definition show_all e h :=
  let (l, t) := show_all' e h
  in (List.rev l, t).
Print show_all.
Print show_all'.

Eval compute in "trace 0 nat/e".
Eval compute in show_all (E_Trace zero E_Nat) 25.

Eval compute in "cons/e (trace 0 nat/e) (trace 1 nat/e)".
Eval compute in show_all (E_Pair (E_Trace zero E_Nat) (E_Trace one E_Nat)) 25.

Eval compute in "or/e (trace 0 nat/e) (trace 1 nat/e)".
Eval compute in show_all (E_Sum  (E_Trace zero E_Nat) (E_Trace one E_Nat)) 25.

(* TODO: map/e example? *)

(* TODO: probably a more useful dep/e could be done here *)
Eval compute in "dep/e (trace 0 nat/e) (n => if even (trace 1 nat/e) else (trace 2 nat/e))".
Eval compute in show_all (E_Dep (E_Trace zero E_Nat)
                                (fun n =>
                                   match n with
                                     | V_Nat n => 
                                       if Even.even_odd_dec n
                                       then (E_Trace one E_Nat)
                                       else (E_Trace two E_Nat)
                                     | _ => (E_Trace three E_Nat) (* never happens *)
                                   end)) 25.
