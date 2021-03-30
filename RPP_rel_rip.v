Require Import Unicode.Utf8 List ZArith String.
Import ListNotations.

Open Scope Z_scope.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition total_map (A : Type) := string → A.
Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition state := total_map Z.

Inductive exp : Type :=
  | EId (x : string)
  | ESu (a1 : exp)
  | EPr (a1 : exp)
  | ENe (a1 : exp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".

Coercion EId : string >-> exp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
  (in custom com at level 0, only parsing,
  f constr at level 0, x constr at level 9,
  y constr at level 9) : com_scope.
Notation "'Su' x" := (ESu x) (in custom com at level 50, left associativity).
Notation "'Pr' x" := (EPr x) (in custom com at level 50, left associativity).
Notation "'Ne' x" := (ENe x) (in custom com at level 50, left associativity).

Open Scope com_scope.

Definition example_exp : exp := <{ Ne (Su X) }>.

Fixpoint eval (st : state) (e : exp) : Z :=
  match e with
  | EId x => st x
  | <{Su e}> => (eval st e) + 1
  | <{Pr e}> => (eval st e) - 1
  | <{Ne e}> => - (eval st e)
  end.

Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Example aexp1 :
  eval (X !-> 5) <{ Ne (Su (Su (Pr X)))}> = -6.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip
  | CSeq (c1 c2 : com)
  | CIf (e : exp) (c1 c2 c3 : com)
  | CItN (n : nat) (c : com)
  | CItZ (e : exp) (c : com).

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'positive' { y } 'zero' { z } 'negative' { w }" :=
         (CIf x y z w)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'itN' x { y }" :=
         (CItN x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Notation "'it' x { y }" :=
         (CItZ x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Reserved Notation
  "l '=[' c ']=>' l'"
  (at level 40, c custom com at level 99,
  l constr, l' constr at next level).

Inductive ceval : com → state → state → Prop :=
  | E_Skip : ∀ st,
      st =[ skip ]=> st
  | E_Ass : ∀ st a n x,
      aeval st a = n →
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : ∀ c1 c2 st st' st'',
      st =[ c1 ]=> st' →
      st' =[ c2 ]=> st'' →
      st =[ c1 ; c2 ]=> st''
  | E_IfPositive : ∀ st st' e c1 c2 c3,
      eval st e > 0 →
      st =[ c1 ]=> st' →
      st =[ if e positive { c1 } zero { c2 } negative { c3 } ]=> st'
  | E_IfZero : ∀ st st' e c1 c2 c3,
      eval st e = 0 →
      st =[ c2 ]=> st' →
      st =[ if e positive { c1 } zero { c2 } negative { c3 } ]=> st'
  | E_IfNegative : ∀ st st' e c1 c2 c3,
      eval st e < 0 →
      st =[ c3 ]=> st' →
      st =[ if e positive { c1 } zero { c2 } negative { c3 } ]=> st'
  | E_ItN : ∀ st st' st'' n c,
      ceval (CItN n c) st st' →
      st' =[ c ]=> st'' →
      ceval (CItN (S n) c) st st'
  | E_ItZ : ∀ st st' e c,
      ceval (CItN (Z.abs_nat(eval st e)) c) st st' →
      st =[ c ]=> st'

  where "st =[ c ]=> st'" := (ceval c st st').

Example eval_example1:
  (Y !-> 4; X !-> 2) =[ skip ]=> (Y !-> 4; X !-> 6).
Proof.
