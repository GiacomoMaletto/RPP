Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
Require Import LibTactics.

(** https://stackoverflow.com/questions/24720137/inverts-produces-unexpected-existt-in-coq **)
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Open Scope Z_scope.

Inductive RPP : nat → Type :=
  | Id : RPP 1
  | Ne : RPP 1
  | Su : RPP 1
  | Pr : RPP 1
  | Sw : RPP 2
  | Co {j : nat}   (f g : RPP j)           : RPP j
  | Pa {j k: nat}  (f : RPP j) (g : RPP k) : RPP (j + k)
  | It {j : nat}   (f : RPP j)             : RPP (j + 1)
  | If {j : nat}   (f g h : RPP j)         : RPP (j + 1).

Fixpoint inv {j : nat} (f : RPP j) : RPP j :=
  match f with
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

Lemma double_inverse : ∀ {n} (f : RPP n),
  inv (inv f) = f.
Proof. induction f; try constructor; try simpl; congruence. Qed.

Reserved Notation
  "l '<=[' c ']=>' l'"
  (at level 40,
  l constr, l' constr at next level).

Inductive rel : forall {j}, RPP j → list Z → list Z → Prop :=
  | E_Id : ∀ n,
      [n] <=[ Id ]=> [n]
  | E_Ne : ∀ n,
      [n] <=[ Ne ]=> [-n]
  | E_Su : ∀ n,
      [n] <=[ Su ]=> [n + 1]
  | E_Pr : ∀ n,
      [n] <=[ Pr ]=> [n - 1]
  | E_Sw : ∀ n m,
      [n; m] <=[ Sw ]=> [m; n]
  | E_Co : ∀ {j} (f g : RPP j) l l' l'',
      l <=[ f ]=> l' →
      l' <=[ g ]=> l'' →
      l <=[ Co f g ]=> l''
  | E_Pa : ∀ {j k} (f : RPP j) (g : RPP k) l1 l1' l2 l2',
      l1 <=[ f ]=> l1' →
      l2 <=[ g ]=> l2' →
      (l1++l2) <=[ Pa f g ]=> (l1'++l2')
  | E_ItZ : ∀ {j} (f : RPP j) l,
      (l++[0]) <=[ It f ]=> (l++[0])
  | E_ItP : ∀ {j} (f : RPP j) p l l' l'',
      (l ++ [Z.pos p - 1]) <=[ It f ]=> (l' ++ [Z.pos p - 1]) →
      l' <=[ f ]=> l'' →
      (l ++ [Z.pos p]) <=[ It f ]=> (l'' ++ [Z.pos p])
  | E_ItN : ∀ {j} (f : RPP j) p l l' l'',
      (l ++ [Z.neg p + 1]) <=[ It f ]=> (l' ++ [Z.neg p + 1]) →
      l' <=[ f ]=> l'' →
      (l ++ [Z.neg p]) <=[ It f ]=> (l'' ++ [Z.neg p])
  | E_IfP : ∀ {j} (f g h : RPP j) n l l',
      n > 0 →
      l <=[ f ]=> l' →
      (l++[n]) <=[ If f g h ]=> (l'++[n])
  | E_IfZ : ∀ {j} (f g h : RPP j) n l l',
      n = 0 →
      l <=[ g ]=> l' →
      (l++[n]) <=[ If f g h ]=> (l'++[n])
  | E_IfN : ∀ {j} (f g h : RPP j) n l l',
      n < 0 →
      l <=[ h ]=> l' →
      (l++[n]) <=[ If f g h ]=> (l'++[n])

  where "l <=[ f ]=> l'" := (rel f l l').

Create HintDb relDb.
Hint Constructors rel : relDb.

Lemma Z_neg_pos_succ : ∀ p, Z.neg (Pos.succ p) = Z.pred (Z.neg p).
Proof. intuition. Qed.

Proposition Z_pos_ind : ∀ P : Z → Prop, P 0 →
  (∀ p : positive, P (Z.pos p - 1) → P (Z.pos p)) →
  (∀ p : positive, P (Z.neg p + 1) → P (Z.neg p)) →
  ∀ z : Z, P z.
Proof.
  intros. destruct z;
  try induction p using Pos.peano_ind; try auto.
  - rewrite Pos2Z.inj_succ. 
    replace (Z.pos p) with (Z.pred(Z.succ(Z.pos p))) in IHp; intuition.
    applys H0 IHp.
  - rewrite Z_neg_pos_succ.
    replace (Z.neg p) with (Z.succ(Z.pred(Z.neg p))) in IHp; intuition.
    applys H1 IHp.
Qed.

Lemma it_ex : ∀ {j} (f : RPP j) l l',
  l <=[ It f ]=> l' → ∃ l1 l1' x,
  l = l1 ++ [x] ∧ l' = l1' ++ [x].
Proof.
  intros. inverts keep H.
  - exists l1 l1 0. intuition.
  - exists l1 l'' (Z.pos p). intuition.
  - exists l1 l'' (Z.neg p). intuition.
Qed.

Ltac all_app_inj_tail := 
  repeat match goal with
  | H : _ |- _ => apply app_inj_tail in H; destruct H end;
  try congruence.

Lemma it_0: ∀ {j} (f : RPP j) l l',
  (l ++ [0]) <=[ It f ]=> (l' ++ [0]) → l = l'.
Proof. intros. inverts H; all_app_inj_tail. Qed.

Lemma it_p: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  (l++[Z.pos p-1]) <=[ It f ]=> (l''++[Z.pos p-1]) ∧
  l'' <=[ f ]=> l'.
Proof.
  intros. inverts H; all_app_inj_tail.
  assert(p = p0). congruence. subst. eauto.
Qed.

Lemma it_n: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.neg p]) <=[ It f ]=> (l' ++ [Z.neg p]) → ∃ l'',
  (l++[Z.neg p+1]) <=[ It f ]=> (l''++[Z.neg p+1]) ∧
  l'' <=[ f ]=> l'.
Proof.
  intros. inverts H; all_app_inj_tail.
  assert(p = p0). congruence. subst. eauto.
Qed.

Lemma it_p_rev: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.pos p-1]) <=[ It f ]=> (l'++[Z.pos p-1]).
Proof.
  intros.
  gen l. gen l'.
  induction p using Pos.peano_ind.
  - intros. lets (l0 & H0 & H1) : @it_p H.
    apply it_0 in H0. subst.
    exists l'. intuition.
  - intros. lets (l0 & H0 & H1) : @it_p H.
    replace (Z.pos (Pos.succ p) - 1) with (Z.pos p) in *; intuition.
    apply IHp in H0. lets (l'' & H2 & H3) : H0.
    exists l''. intuition.
    eapply E_ItP; eauto.
Qed.

Lemma it_n_rev: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.neg p]) <=[ It f ]=> (l' ++ [Z.neg p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.neg p+1]) <=[ It f ]=> (l'++[Z.neg p+1]).
Proof.
  intros.
  gen l. gen l'.
  induction p using Pos.peano_ind.
  - intros. lets (l0 & H0 & H1) : @it_n H.
    apply it_0 in H0. subst.
    exists l'. intuition.
  - intros. lets (l0 & H0 & H1) : @it_n H.
    replace (Z.neg (Pos.succ p) + 1) with (Z.neg p) in *; intuition.
    apply IHp in H0. lets (l'' & H2 & H3) : H0.
    exists l''. intuition.
    eapply E_ItN; eauto.
Qed.

Proposition proposition_1_r : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' → l' <=[ inv f ]=> l.
Proof.
  induction f; intros.
  - inverts H. intuition.
  - inverts H. replace n with (--n) at 2; intuition.
  - inverts H. replace n with ((n+1)-1) at 2; intuition.
  - inverts H. replace n with ((n-1)+1) at 2; intuition.
  - inverts H. intuition.
  - inverts H. eapply E_Co; eauto.
  - inverts H. eapply E_Pa; eauto.
  - lets (l1 & l1' & n & H1 & H1') : @it_ex H. subst.
    gen l1. gen l1'.
    induction n using Z_pos_ind.
    + intros. apply it_0 in H. rewrite H. constructor.
    + intros. lets (l' & H0 & H1) : @it_p_rev H.
      eapply E_ItP; eauto.
    + intros. lets (l' & H0 & H1) : @it_n_rev H.
      eapply E_ItN; eauto.
  - inverts H; [eapply E_IfP | eapply E_IfZ | eapply E_IfN]; eauto.
Qed.

Proposition proposition_1_l : ∀ {j} (f : RPP j) l l',
  l <=[ inv f ]=> l' → l' <=[ f ]=> l.
Proof.
  intros. rewrite <- double_inverse at 1.
  apply proposition_1_r. assumption.
Qed.

Proposition proposition_1 : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l'<-> l' <=[ inv f ]=> l.
Proof. split; [apply proposition_1_r | apply proposition_1_l]. Qed.

Definition inc := It Su.
Proposition inc_rel : ∀ n m,
  [n; m] <=[inc]=> [n + Z.abs m; m].
Proof.
  intros. unfold inc.
  induction m using Z_pos_ind.
  - rewrite Z.add_0_r. exact (E_ItZ Su [n]).
  - pose( E_Su (n + (Z.abs (Z.pos p - 1))) ).
    replace (n+Z.abs(Z.pos p-1)+1) with (n+Z.abs(Z.pos p)) in r; intuition.
    apply (E_ItP Su p [n] [n+Z.abs(Z.pos p-1)] [n+Z.abs(Z.pos p)]); intuition.
  - pose( E_Su (n + (Z.abs (Z.neg p + 1)))).
    replace (n+Z.abs(Z.neg p+1)+1) with (n+Z.abs(Z.neg p)) in r; intuition.
    apply (E_ItN Su p [n] [n+Z.abs(Z.neg p+1)] [n+Z.abs(Z.neg p)]); intuition.
Qed.

Definition dec := inv inc.
Proposition dec_rel : ∀ n m,
  [n; m] <=[dec]=> [n - (Z.abs m); m].
Proof.
  intros. remember (n - Z.abs m) as n'.
  replace n with (n' + Z.abs m); intuition.
  unfold dec. rewrite proposition_1.
  apply inc_rel.
Qed.