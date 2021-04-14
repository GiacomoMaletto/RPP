Require Import Unicode.Utf8 ZArith String.
(* Da Logical Foundations *)
Require Import Maps.

Open Scope Z_scope.
Open Scope string_scope.

Inductive com : Type :=
  | CSk
  | CNe (x : string)
  | CSu (x : string)
  | CPr (x : string)
  | CSw (x y : string)
  | CCo (c1 c2 : com)
  | CIt (x : string) (c1 : com)
  | CIf (x : string) (c1 c2 c3 : com).

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e
  (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x
  (in custom com at level 0, x at level 200) : com_scope.
Notation "{ x }" := x
  (in custom com at level 0, x constr at level 98) : com_scope.
Notation "x" := x
  (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x" := (f x)
  (in custom com at level 0, only parsing) : com_scope.
Notation "'skip'" := CSk
  (in custom com at level 0) : com_scope.
Notation "'neg'" := CNe
  (in custom com at level 0) : com_scope.
Notation "'succ'" := CSu
  (in custom com at level 0) : com_scope.
Notation "'pred'" := CPr
  (in custom com at level 0) : com_scope.
Notation "x <=> y" := (CSw x y)
  (in custom com at level 0) : com_scope.
Notation "c1 ; c2" := (CCo c1 c2)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'repeat' x 'do' c1 'end'" := (CIt x c1)
  (in custom com at level 89, x at level 99, c1 at level 99) : com_scope.
Notation "'if' x 'positive' c1 'zero' c2 'negative' c3 'end'" := (CIf x c1 c2 c3)
  (in custom com at level 89, x at level 99,
  c1 at level 99, c2 at level 99, c3 at level 99) : com_scope.

Open Scope com_scope.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Check
  <{if X positive
      repeat Y do succ X end
    zero skip
    negative
      repeat Y do pred X end
    end}>.

Fixpoint inv (c : com) : com :=
  match c with
  | CSk => CSk
  | CNe x => CNe x
  | CSu x => CPr x
  | CPr x => CSu x
  | CSw x y => CSw x y
  | CCo c1 c2 => CCo (inv c2) (inv c1)
  | CIt x c1 => CIt x (inv c1)
  | CIf x c1 c2 c3 => CIf x (inv c1) (inv c2) (inv c3)
  end.

Lemma double_inverse : ∀ c, inv (inv c) = c.
Proof. induction c; try constructor; try simpl; congruence. Qed.

Definition varst := total_map bool.
Definition empty_varst : varst := t_empty false.
Notation "![ ]!" := empty_varst (format "![ ]!").
Notation "![ x ]!" := (t_update empty_varst x true).
Notation "![ x !! y !! .. !! z ]!" :=
  (t_update (t_update .. (t_update empty_varst z true) .. y true) x true).

Fixpoint comvarst (c : com) : varst :=
  match c with
  | CSk => ![]!
  | CNe x => ![x]!
  | CSu x => ![x]!
  | CPr x => ![x]!
  | CSw x y => ![x !! y]!
  | CCo c1 c2 => empty_varst
  | CIt x c1 => empty_varst
  | CIf x c1 c2 c3 => empty_varst
  end.

Definition state := partial_map Z.
Definition empty_st : state := empty.

Reserved Notation
  "l '<=[' c ']=>' l'"
  (at level 40, c custom rpp at level 99,
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
  | E_IfTrue : ∀ st st' b c1 c2,
      beval st b = true →
      st =[ c1 ]=> st' →
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : ∀ st st' b c1 c2,
      beval st b = false →
      st =[ c2 ]=> st' →
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      st =[ while b do c end ]=> st
  | E_WhileTrue : ∀ st st' st'' b c,
      beval st b = true →
      st =[ c ]=> st' →
      st' =[ while b do c end ]=> st'' →
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').











