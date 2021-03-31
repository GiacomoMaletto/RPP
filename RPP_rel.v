Require Import Unicode.Utf8 List ZArith Lia Permutation.
Import ListNotations.
Require Import LibTactics.

Open Scope Z_scope.

Inductive RPP : Type :=
  | Nu : RPP
  | Id : RPP
  | Ne : RPP
  | Su : RPP
  | Pr : RPP
  | Sw : RPP
  | Co : RPP → RPP → RPP
  | Pa : RPP → RPP → RPP
  | It : RPP → RPP
  | If : RPP → RPP → RPP → RPP.

Fixpoint inv (f : RPP) : RPP :=
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

Lemma double_inverse : ∀ f, inv (inv f) = f.
Proof. induction f; try constructor; try simpl; congruence. Qed.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
  (in custom com at level 0, only parsing,
  f constr at level 0, x constr at level 9,
  y constr at level 9) : com_scope.
Notation "f ; g" := (Co f g) (in custom com at level 50, right associativity).
Notation "f ‖ g" := (Pa f g) (in custom com at level 50, right associativity).

Open Scope com_scope.

Reserved Notation
  "l '<=[' c ']=>' l'"
  (at level 40, c custom com at level 99,
  l constr, l' constr at next level).

Inductive RPP_rel : RPP → list Z → list Z → Prop :=
  | E_Nu :
      [] <=[ Nu ]=> []
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
  | E_Co : ∀ f g l l' l'',
      l <=[ f ]=> l' →
      l' <=[ g ]=> l'' →
      l <=[ f ; g ]=> l''
  | E_Pa : ∀ f g l1 l1' l2 l2',
      l1 <=[ f ]=> l1' →
      l2 <=[ g ]=> l2' →
      (l1++l2) <=[ f ‖ g ]=> (l1'++l2')
  | E_ItZ : ∀ f l,
      (l++[0]) <=[ It f ]=> (l++[0])
  | E_ItP : ∀ f p l l' l'',
      (l ++ [Z.pos p - 1]) <=[ It f ]=> (l' ++ [Z.pos p - 1]) →
      l' <=[ f ]=> l'' →
      (l ++ [Z.pos p]) <=[ It f ]=> (l'' ++ [Z.pos p])
  | E_ItN : ∀ f p l l' l'',
      (l ++ [Z.neg p + 1]) <=[ It f ]=> (l' ++ [Z.neg p + 1]) →
      l' <=[ f ]=> l'' →
      (l ++ [Z.neg p]) <=[ It f ]=> (l'' ++ [Z.neg p])
  | E_IfP : ∀ f g h n l l',
      n > 0 →
      l <=[ f ]=> l' →
      (l++[n]) <=[ If f g h ]=> (l'++[n])
  | E_IfZ : ∀ f g h n l l',
      n = 0 →
      l <=[ g ]=> l' →
      (l++[n]) <=[ If f g h ]=> (l'++[n])
  | E_IfN : ∀ f g h n l l',
      n < 0 →
      l <=[ h ]=> l' →
      (l++[n]) <=[ If f g h ]=> (l'++[n])

  where "l <=[ f ]=> l'" := (RPP_rel f l l').

Create HintDb RPP_Db.
#[export] Hint Constructors RPP_rel : RPP_Db.

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

Lemma it_ex : ∀ f l l',
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

Lemma it_0: ∀ f l l',
  (l ++ [0]) <=[ It f ]=> (l' ++ [0]) → l = l'.
Proof. intros. inverts H; all_app_inj_tail. Qed.

Lemma it_p: ∀ f l l' p,
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  (l++[Z.pos p-1]) <=[ It f ]=> (l''++[Z.pos p-1]) ∧
  l'' <=[ f ]=> l'.
Proof.
  intros. inverts H; all_app_inj_tail.
  assert(p = p0). congruence. subst. eauto.
Qed.

Lemma it_n: ∀ f l l' p,
  (l ++ [Z.neg p]) <=[ It f ]=> (l' ++ [Z.neg p]) → ∃ l'',
  (l++[Z.neg p+1]) <=[ It f ]=> (l''++[Z.neg p+1]) ∧
  l'' <=[ f ]=> l'.
Proof.
  intros. inverts H; all_app_inj_tail.
  assert(p = p0). congruence. subst. eauto.
Qed.

Lemma it_p_rev: ∀ f l l' p,
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.pos p-1]) <=[ It f ]=> (l'++[Z.pos p-1]).
Proof.
  intros.
  gen l l'.
  induction p using Pos.peano_ind.
  - intros. lets (l0 & H0 & H1) : it_p H.
    apply it_0 in H0. subst.
    exists l'. intuition.
  - intros. lets (l0 & H0 & H1) : it_p H.
    replace (Z.pos (Pos.succ p) - 1) with (Z.pos p) in *; intuition.
    apply IHp in H0. lets (l'' & H2 & H3) : H0.
    exists l''. intuition.
    eapply E_ItP; eauto.
Qed.

Lemma it_n_rev: ∀ f l l' p,
  (l ++ [Z.neg p]) <=[ It f ]=> (l' ++ [Z.neg p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.neg p+1]) <=[ It f ]=> (l'++[Z.neg p+1]).
Proof.
  intros.
  gen l l'.
  induction p using Pos.peano_ind.
  - intros. lets (l0 & H0 & H1) : it_n H.
    apply it_0 in H0. subst.
    exists l'. intuition.
  - intros. lets (l0 & H0 & H1) : it_n H.
    replace (Z.neg (Pos.succ p) + 1) with (Z.neg p) in *; intuition.
    apply IHp in H0. lets (l'' & H2 & H3) : H0.
    exists l''. intuition.
    eapply E_ItN; eauto.
Qed.

Proposition proposition_1_r : ∀ f l l',
  l <=[ f ]=> l' → l' <=[ inv f ]=> l.
Proof.
  induction f; intros.
  - inverts H. intuition.
  - inverts H. intuition.
  - inverts H. replace n with (--n) at 2; intuition.
  - inverts H. replace n with ((n+1)-1) at 2; intuition.
  - inverts H. replace n with ((n-1)+1) at 2; intuition.
  - inverts H. intuition.
  - inverts H. eapply E_Co; eauto.
  - inverts H. eapply E_Pa; eauto.
  - lets (l1 & l1' & n & H1 & H1') : it_ex H. subst.
    gen l1 l1'.
    induction n using Z_pos_ind.
    + intros. apply it_0 in H. rewrite H. constructor.
    + intros. lets (l' & H0 & H1) : it_p_rev H.
      eapply E_ItP; eauto.
    + intros. lets (l' & H0 & H1) : it_n_rev H.
      eapply E_ItN; eauto.
  - inverts H; [eapply E_IfP | eapply E_IfZ | eapply E_IfN]; eauto.
Qed.

Proposition proposition_1_l : ∀ f l l',
  l <=[ inv f ]=> l' → l' <=[ f ]=> l.
Proof.
  intros. rewrite <- double_inverse at 1.
  apply proposition_1_r. assumption.
Qed.

Proposition proposition_1 : ∀ f l l',
  l <=[ f ]=> l' <-> l' <=[ inv f ]=> l.
Proof. split; [apply proposition_1_r | apply proposition_1_l]. Qed.

Definition inc := It Su.
Proposition inc_rel : ∀ n m,
  [n; m] <=[inc]=> [n + Z.abs m; m].
Proof.
  intros. unfold inc.
  induction m using Z_pos_ind.
  - rewrite Z.add_0_r. exact (E_ItZ Su [n]).
  - pose( E_Su (n + (Z.abs (Z.pos p - 1))) ).
    replace (n+Z.abs(Z.pos p-1)+1)
    with (n+Z.abs(Z.pos p)) in r; intuition.
    applys E_ItP Su p [n] [n+Z.abs(Z.pos p-1)] [n+Z.abs(Z.pos p)];
    intuition.
  - pose( E_Su (n + (Z.abs (Z.neg p + 1))) ).
    replace (n+Z.abs(Z.neg p+1)+1)
    with (n+Z.abs(Z.neg p)) in r; intuition.
    applys E_ItN Su p [n] [n+Z.abs(Z.neg p+1)] [n+Z.abs(Z.neg p)];
    intuition.
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

Fixpoint Co_n (n : nat) (f : RPP) : RPP :=
  match n with
  | O => Nu
  | S O => f
  | S n => <{ f ‖ Co_n n f }>
  end.

Definition Id' n := Co_n n Id.

Lemma Id'_identity : ∀ l,
  l <=[ Id' (length l) ]=> l.
Proof.
  intros.
  remember (length l) as n. gen l.
  induction n.
  - introv H1. cbv.
    symmetry in H1.
    rewrite length_zero_iff_nil in H1. rewrite H1.
    constructor.
  - destruct n.
    + intros. unfold Id'. simpl.
      destruct l; try discriminate.
      asserts_rewrite(l = []).
      { injection Heqn as H.
        apply length_zero_iff_nil. auto. }
      constructor.
    + intros. unfold Id'. simpl.
      destruct l; try discriminate.
      assert(S n = length l); intuition.
      apply IHn in H.
      pose (E_Id z).
      applys E_Pa Id [z] [z] l l; intuition.
Qed.

Proposition RPP_perm : ∀ {l l'} (p : Permutation l l'),
  ∃ f, l <=[ f ]=> l'.
Proof.
  intros.
  induction p.
  - exists Nu. constructor.
  - lets f H : IHp.
    exists <{ Id ‖ f }>.
    pose (E_Id x).
    applys E_Pa f r H.
  - exists <{ Sw ‖ Id' (length l) }>.
    pose (E_Sw y x).
    pose (Id'_identity l).
    applys E_Pa Sw [y;x] [x;y] l; intuition.
  - lets f1 H1 : IHp1.
    lets f2 H2 : IHp2.
    exists <{ f1 ; f2 }>.
    eapply E_Co; eauto.
Qed.