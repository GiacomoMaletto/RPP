Require Import Unicode.Utf8 List ZArith Lia Permutation.
Import ListNotations.
Require Import LibTactics.
Set Implicit Arguments.

Inductive RPP : nat → Type :=
  | Nu : RPP 0
  | Id : RPP 1
  | Ne : RPP 1
  | Su : RPP 1
  | Pr : RPP 1
  | Sw : RPP 2
  | Co n (f g : RPP n) : RPP n
  | Pa n m (f : RPP n) (g : RPP m) : RPP (n + m)
  | It n (f : RPP n) : RPP (S n)
  | If n (f g h : RPP n) : RPP (S n).

Notation "f ;; g" := (Co f g) (at level 65, left associativity).
(* \Vert *)
Notation "f ‖ g" := (Pa f g) (at level 65, left associativity).

Fixpoint inv n (f : RPP n) : RPP n :=
  match f with
  | Nu => Nu
  | Id => Id
  | Ne => Ne
  | Su => Pr
  | Pr => Su
  | Sw => Sw
  | Co f g => Co (inv g) (inv f)
  | Pa f g => Pa (inv f) (inv g)
  | It f => It (inv f)
  | If f g h => If (inv f) (inv g) (inv h)
  end.

Lemma inv_involute : ∀ n (f : RPP n), inv (inv f) = f.
Proof. induction f; try constructor; simpl; congruence. Qed.

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

Open Scope Z_scope.

Fixpoint evaluate n (f : RPP n) (l : list Z) : list Z :=
  match f with
  | Nu => l
  | Id => l
  | Ne => match l with []=>l | x::l' => -x :: l' end
  | Su => match l with []=>l | x::l' => x+1 :: l' end
  | Pr => match l with []=>l | x::l' => x-1 :: l' end
  | Sw => match l with x::y::l' => y::x::l' | _=>l end
  | Co f g => (evaluate g) (evaluate f l)
  | @Pa n _ f g =>
    (evaluate f (firstn n l)) ++ (evaluate g (skipn n l))
  | It f => match l with []=>l
    | x::l' => x::iter (evaluate f) (Z.abs_nat x) l' end
  | If f g h => match l with []=>l
    | x::l' => match x with
      | Zpos p => x::(evaluate f) l'
      | Z0 => x::(evaluate g) l'
      | Zneg p => x::(evaluate h) l'
      end
    end
  end.

(* \laquo f \raquo *)
Notation "« f »" := (evaluate f).

Lemma evaluate_nil : ∀ n (f : RPP n), «f» [] = [].
Proof.
  induction f; try reflexivity.
  - simpl. congruence.
  - simpl. rewrite firstn_nil. rewrite skipn_nil.
    rewrite IHf1. rewrite IHf2. reflexivity.
Qed.

Ltac nil_case l := destruct l;
  try rewrite !evaluate_nil; try reflexivity.

Lemma length_evaluate : ∀ n (f : RPP n) (l : list Z),
  length («f» l) = length l.
Proof.
  intros. gen l.
  induction f; try nil_case l; intros.
  - nil_case l.
  - simpl. rewrite IHf2. rewrite IHf1. reflexivity.
  - simpl. rewrite app_length.
    rewrite IHf1. rewrite IHf2.
    rewrite <- app_length. rewrite firstn_skipn. reflexivity.
  - simpl. induction (Z.abs_nat z); auto. simpl. rewrite IHf; lia.
  - destruct z; simpl; congruence.
Qed.

Ltac liast :=
  try rewrite length_evaluate; try rewrite evaluate_nil;
  try rewrite firstn_length; try rewrite skipn_length;
  try rewrite app_nil_r;
  simpl; try lia; auto.

Theorem proposition_2 : ∀ n m (f g : RPP n) (f' g' : RPP m) l,
  «(f‖f');;(g‖g')» l = «(f;;g)‖(f';;g')» l.
Proof.
  intros. simpl.
  rewrite firstn_app. rewrite skipn_app.
  rewrite length_evaluate.
  destruct (Nat.le_ge_cases (length l) n).
  - rewrite !firstn_all2. rewrite !skipn_all2.
    rewrite !evaluate_nil. rewrite !app_nil_r. reflexivity.
    all : liast.
  - assert (length (firstn n l) = n). liast. rewrite H0.
    asserts_rewrite (n - n = 0)%nat. lia.
    replace (firstn n _) with (« f » (firstn n l)).
    replace (skipn n (« f » (firstn n l))) with ([]:list Z).
    rewrite firstn_O. rewrite skipn_O. liast.
    rewrite skipn_all2; liast.
    remember (« f » (firstn n l)).
    rewrite firstn_all2; subst; liast.
Qed.

Lemma iter_succ : ∀ X (f : X → X) n x,
  iter f (S n) x = f (iter f n x).
Proof. reflexivity. Qed.

Lemma iter_comm : ∀ X (f g : X → X), (∀ x, f (g x) = g (f x)) →
  ∀ n x, f (iter g n x) = iter g n (f x).
Proof.
  intros. induction n. reflexivity.
  rewrite iter_succ. rewrite H. rewrite IHn. reflexivity.
Qed.

Lemma iter_inverse : ∀ X (f g : X → X), (∀ x, f (g x) = x) →
  ∀ n x, iter f n (iter g n x) = x.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite iter_comm; auto. rewrite H. assumption.
Qed.

Lemma co_if : ∀ n (f g h f' g' h': RPP n) l,
  «If f g h;;If f' g' h'» l = «If (f;;f') (g;;g') (h;;h') » l.
Proof.
  intros. nil_case l.
  simpl. destruct z; reflexivity.
Qed.

Theorem proposition_1_l : ∀ n (f : RPP n) l,
  «f;;inv f» l = l.
Proof.
  intros. gen l. induction f; try (nil_case l; simpl; f_equal; lia).
  - nil_case l. nil_case l.
  - intros. simpl in *. congruence.
  - intros. simpl inv. rewrite proposition_2.
    simpl in *. rewrite IHf1. rewrite IHf2. apply firstn_skipn.
  - nil_case l. simpl. rewrite iter_inverse; auto.
  - nil_case l. simpl inv. rewrite co_if. simpl in *.
    destruct z; congruence.
Qed.

Theorem proposition_1_r : ∀ n (f : RPP n) l,
  «inv f;;f» l = l.
Proof.
  intros. rewrite <- (inv_involute f) at 2. apply proposition_1_l.
Qed.

Fixpoint Id' n : RPP n :=
  match n  with
    | O => Nu
    | S n' => Id ‖ Id' n'
  end.

Lemma id'_identity : ∀ n l,
  «Id' n» l = l.
Proof.
  intros n. induction n. reflexivity.
  unfold Id'. fold Id'. simpl.
  destruct l; rewrite IHn; reflexivity.
Qed.

Fixpoint Sw' i n : RPP n :=
  match i, n with
  | _, O => Nu
  | O, S m => Id' (S m)
  | S O, S (S m) => Sw ‖ Id' m
  | S j, S m => Id ‖ Sw' j m
  end.

Fixpoint call i n : RPP n :=
  match i with
  | O => Id' n
  | S j => Sw' j n ;; call j n
  end.

Fixpoint call_list (l : list nat) n :=
  match l with
  | [] => Id' n
  | i::l => call i n ;; call_list l n
  end.

Fixpoint prepared (l : list nat) :=
  match l with
  | [] => []
  | i :: l' => i + length (filter (λ j, i <? j) l') :: prepared l'
  end%nat.

Definition perm (l : list nat) n := call_list (rev (prepared l)) n.

Notation "\ l \^ n" := (perm l n) (at level 50).

Compute «\[5;2;3;6]\^8»%nat [1;2;3;4;5;6;7;8].

Open Scope nat_scope.
Definition cast n (f : RPP n) m : RPP m.
  remember (n <=? m).
  destruct b.
  - pose (f ‖ Id' (m - n)).
    assert (n + (m - n) = m).
      apply le_plus_minus_r. apply Nat.leb_le. auto.
    rewrite H in r. exact r.
  - exact (Id' m).
Defined.

Compute cast Su 1.

Program Definition cast n (f : RPP n) m : RPP m :=
  match (n <=? m)%nat with
  | true => f ‖ Id' (m - n)
  | false => Id' m
  end.
Next Obligation.
  apply le_plus_minus_r.
  apply Nat.leb_le.
  symmetry. assumption.
Defined.

Definition It' i l m n (f : RPP n) := \i :: l\^m;;cast (It f) m;;inv(\i :: l\^m).

Definition inc j i m := It' i [j] m Su.

Goal «cast Su 1» [1;2;3;4;5] = [2;2;3;4;5].
Proof.
  unfold cast. simpl. cbv.







