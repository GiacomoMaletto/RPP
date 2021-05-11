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

Definition state := string → Z.

Definition empty : state := λ _, 0.
Definition update (st : state) x o : state :=
  λ y, if x =? y then o else st y.

(* \map *)
Notation "x ↦ n ; st" := (update st x n)
  (at level 100, n at next level, right associativity).
Notation "x ↦ n" := (update empty x  n)
  (at level 100).

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | O => x
  | S n => f (iter f n x)
  end.

Fixpoint evaluate (f : RPPM) (st : state) : state :=
  match f with
  | Id => st
  | Ne x => x ↦ -(st x); st
  | Su x => x ↦ st x + 1; st
  | Pr x => x ↦ st x - 1; st
  | Co f g => (evaluate g) (evaluate f st)
  | It x f => iter (evaluate f) (Z.abs_nat (st x)) st
  | If x f g h => evaluate (match st x with
    | Zpos _ => f
    | Z0 => g
    | Zneg _ => h
    end) st
  end.

(* \laq f \raq *)
Notation "« f »" := (evaluate f).

Fixpoint inb x l : bool :=
  match l with
  | [] => false
  | y::l => (x =? y) || (inb x l)
  end.

Fixpoint bad' (f : RPPM) (l : list string) : bool :=
  match f with
  | Id => false
  | Ne x => inb x l
  | Su x => inb x l
  | Pr x => inb x l
  | Co f g => bad' f l || bad' g l
  | It x f => bad' f (x :: l)
  | If x f g h => bad' f (x :: l) || bad' g (x :: l) || bad' h (x :: l)
  end.

Definition bad (f : RPPM) := bad' f [].

Fixpoint modified' (f : RPPM) l :=
  match f with
  | Id => []
  | Ne x => x :: l
  | Su x => x :: l
  | Pr x => x :: l
  | Co f g => modified' g (modified' f l)
  | It x f => modified' f l
  | If x f g h => modified' h (modified' g (modified' f l))
  end.

Fixpoint nodup_str l :=
  match l with
  | [] => []
  | x :: l => if inb x l then nodup_str l else x :: nodup_str l
  end.

Definition modified (f : RPPM) := nodup_str (modified' f []).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".

Definition inc := It Y (Su X).

Fixpoint eq_each X Y (f g : X → Y) (l : list X) :=
  match l with
  | [] => True
  | x :: [] => f(x) = g(x)
  | x :: l => f(x) = g(x) ∧ eq_each f g l
  end.

Theorem eq_modified : ∀ f st st', «f» st = st' ↔
  eq_each («f» st) st' (modified f).
Admitted.

Lemma inc_good : bad inc = false.
Proof. reflexivity. Qed.

Goal ∀ x, (modified (Ne x;; Ne x)) = [x].
Proof.
  intros. unfold modified. simpl. rewrite eqb_refl. reflexivity.
Qed.

Proposition inc_def : ∀ st,
  «inc» st = (X ↦ (st X) + (Z.abs (st Y)); st).
Proof.
  intros. apply eq_modified. simpl.
  rewrite <- Zabs2Nat.id_abs.
  remember (Z.abs_nat (st Y)) as n.
  induction n.
  - cbv. destruct (st "X"); reflexivity.
  - cbv. rewrite IHn.

Definition dec j i := inv (inc j i).
Definition mult k j i := It k (inc j i) ;;
  If k (If j Id Id (Ne i)) Id (If j (Ne i) Id Id).

Proposition 








