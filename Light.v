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
  | Co j (f g : RPP j) : RPP j
  | Pa j k (f : RPP j) (g : RPP k) : RPP (j + k)
  | It j (f : RPP j) : RPP (S j)
  | If j (f g h : RPP j) : RPP (S j).

(* \! *)
Notation "f ;; g" := (Co f g) (at level 65, left associativity).
(* \Vert *)
Notation "f ‖ g" := (Pa f g) (at level 65, left associativity).

Fixpoint inv {j} (f : RPP j) : RPP j :=
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

Lemma inv_involute : ∀ j (f : RPP j), inv (inv f) = f.
Proof. induction f; try constructor; simpl; congruence. Qed.

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

Open Scope Z_scope.

Fixpoint evaluate j (f : RPP j) (l : list Z) : list Z :=
  match f with
  | Nu => l
  | Id => l
  | Ne => match l with []=>l | x::l' => -x :: l' end
  | Su => match l with []=>l | x::l' => x+1 :: l' end
  | Pr => match l with []=>l | x::l' => x-1 :: l' end
  | Sw => match l with x::y::l' => y::x::l' | _=>l end
  | Co f g => (evaluate g) (evaluate f l)
  | @Pa j _ f g =>
    (evaluate f (firstn j l)) ++ (evaluate g (skipn j l))
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

Open Scope nat_scope.

Lemma evaluate_nil : ∀ j (f : RPP j), «f» [] = [].
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

Theorem proposition_2 : ∀ j k (f g : RPP j) (f' g' : RPP k) l,
  «(f‖f');;(g‖g')» l = «(f;;g)‖(f';;g')» l.
Proof.
  intros. simpl.
  rewrite firstn_app. rewrite skipn_app.
  rewrite length_evaluate.
  destruct (Nat.le_ge_cases (length l) j).
  - rewrite !firstn_all2. rewrite !skipn_all2.
    rewrite !evaluate_nil. rewrite !app_nil_r. reflexivity.
    all : liast.
  - assert (length (firstn j l) = j). liast. rewrite H0.
    asserts_rewrite (j - j = 0). lia.
    replace (firstn j _) with (« f » (firstn j l)).
    replace (skipn j (« f » (firstn j l))) with (nil:list Z).
    rewrite firstn_O. rewrite skipn_O. liast.
    rewrite skipn_all2; liast.
    remember (« f » (firstn j l)).
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

Lemma co_if : ∀ j (f g h f' g' h': RPP j) l,
  «If f g h;;If f' g' h'» l = «If (f;;f') (g;;g') (h;;h') » l.
Proof.
  intros. nil_case l.
  simpl. destruct z; reflexivity.
Qed.

Theorem proposition_1_l : ∀ j (f : RPP j) l,
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

Theorem proposition_1_r : ∀ j (f : RPP j) l,
  «inv f;;f» l = l.
Proof.
  intros. rewrite <- (inv_involute f) at 2. apply proposition_1_l.
Qed.

Fixpoint Id' n : RPP n :=
  match n  with
    | 0 => Nu
    | S n' => Id ‖ Id' n'
  end.

Lemma id'_identity : ∀ n l,
  «Id' n» l = l.
Proof.
  intros n. induction n. reflexivity.
  unfold Id'. fold Id'. simpl.
  destruct l; rewrite IHn; reflexivity.
Qed.

Definition w {j} (f : RPP j) n := Id' n ‖ f.

Definition Ne' n := w Ne n.
Definition Su' n := w Su n.
Definition Pr' n := w Pr n.

Proposition ex_rewiring : ∀ l l' (p : Permutation l l'),
  ∃ (f : RPP (length l)), «f» l = l'.
Proof.
  intros. induction p.
  - exists Nu. reflexivity.
  - lets f H : IHp.
    exists (Id ‖ f). simpl. rewrite H. reflexivity. 
  - exists (Sw ‖ Id' (length l)).
    simpl. rewrite id'_identity. reflexivity.
  - assert (length l = length l').
    apply Permutation_length. auto. rewrite <- H in IHp2.
    lets f1 H1 : IHp1.
    lets f2 H2 : IHp2.
    exists (f1 ;; f2). subst. auto.
Qed.









