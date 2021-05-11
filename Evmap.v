Require Import Unicode.Utf8 ZArith List String Lia FunctionalExtensionality.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.

Set Implicit Arguments.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope string_scope.

Inductive RPPM : Type :=
  | Id
  | Ne (x : string)
  | Su (x : string)
  | Pr (x : string)
  | Co (f g : RPPM)
  | It (x : string) (f : RPPM)
  | If (x : string) (f g h : RPPM).

Notation "f ;; g" := (Co f g) (at level 65, left associativity).

Fixpoint inv (f : RPPM) : RPPM :=
  match f with
  | Id => Id
  | Ne x => Ne x
  | Su x => Pr x
  | Pr x => Su x
  | Co f g => Co (inv g) (inv f)
  | It x f => It x (inv f)
  | If x f g h => If x (inv f) (inv g) (inv h)
  end.

Lemma inv_involute : ∀ f, inv (inv f) = f.
Proof.
  intros. induction f; try reflexivity; simpl; congruence.
Qed.

Definition state := string → option Z.

(* \equi *)
Notation "x ≡ y" := (eqb x y) (at level 70).
(* \nequ *)
Notation "x ≢ y" := (negb (eqb x y)) (at level 70).

Definition empty : state := λ _, Some 0.
Definition update (st : state) x o : state :=
  λ y, if x ≡ y then o else st y.

(* \map *)
Notation "x ↦ n ; st" := (update st x (Some n))
  (at level 100, n at next level, right associativity).
Notation "x ↦ n" := (update empty x (Some n))
  (at level 100).
(* \dar *)
Notation "x ↓ ; st" := (update st x None)
  (at level 100, right associativity).
Notation "x ↓" := (update empty x None)
  (at level 100).

Definition raise (o : option Z) : Z :=
  match o with
  | None => 0
  | Some n => n
  end.

(* \uar *)
Notation "↑ o" := (raise o) (at level 0).

Definition is_some (o : option Z) := ∃ n, o = Some n.
Notation "o ?" := (is_some o) (at level 0).

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | O => x
  | S n => f (iter f n x)
  end.

Fixpoint evaluate (f : RPPM) (st : state) : state :=
  match f with
  | Id => st
  | Ne x => match st x with
    | None => st
    | Some n => x ↦ -n; st
    end
  | Su x => match st x with
    | None => st
    | Some n => x ↦ n + 1; st
    end
  | Pr x => match st x with
    | None => st
    | Some n => x ↦ n - 1; st
    end
  | Co f g => (evaluate g) (evaluate f st)
  | It x f => match st x with
    | None => st
    | Some n => x ↦ n; iter (evaluate f) (Z.abs_nat n) (x↓; st)
    end
  | If x f g h => match st x with
    | None => st
    | Some n => x ↦ n; evaluate (match n with
      | Zpos _ => f
      | Z0 => g
      | Zneg _ => h
      end) (x↓; st)
    end
  end.

(* \laq f \raq *)
Notation "« f »" := (evaluate f).

Definition inc j i := It j (Su i).
Definition dec j i := inv (inc j i).
Definition mult k j i := It k (inc j i) ;;
  If k (If j Id Id (Ne i)) Id (If j (Ne i) Id Id).

Proposition inc_def : ∀ j i st, j ≠ i → (st i)? → (st j)? →
  «inc j i» st = (i ↦ ↑(st i) + Z.abs(↑(st j)); st).
Proof.
  intros. destruct H0. destruct H1. rewrite H0. rewrite H1. simpl.









