Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
Import LibTactics.

(** https://stackoverflow.com/questions/24720137/inversion-produces-unexpected-existt-in-coq **)
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
    apply (H0 _ IHp).
  - rewrite Z_neg_pos_succ.
    replace (Z.neg p) with (Z.succ(Z.pred(Z.neg p))) in IHp; intuition.
    apply (H1 _ IHp).
Qed.

Ltac inv_clean H := inversion H;
  repeat match goal with
  | H : _ = _ |- _ => apply inj_pair2_eq_dec in H; trivial;
  try apply eq_nat_dec; try subst end.

Ltac all_app_inj_tail := 
  repeat match goal with
  | H : _ |- _ => apply app_inj_tail in H; destruct H end;
  try congruence.

Lemma it_ex : ∀ {j} (f : RPP j) l l',
  l <=[ It f ]=> l' → ∃ l1 l1' x,
  l = l1 ++ [x] ∧ l' = l1' ++ [x].
Proof.
  intros. inv_clean H.
  - exists l0. exists l0. exists 0. intuition.
  - exists l0. exists l''. exists (Z.pos p). intuition.
  - exists l0. exists l''. exists (Z.neg p). intuition.
Qed.

Lemma it_0: ∀ {j} (f : RPP j) l l',
  (l ++ [0]) <=[ It f ]=> (l' ++ [0]) → l = l'.
Proof. intros. inversion H; all_app_inj_tail. Qed.

Lemma it_p: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  (l++[Z.pos p-1]) <=[ It f ]=> (l''++[Z.pos p-1]) ∧
  l'' <=[ f ]=> l'.
Proof.
  intros. inv_clean H; all_app_inj_tail.
  assert(p = p0). congruence. subst. eauto.
Qed.

Lemma it_n: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.neg p]) <=[ It f ]=> (l' ++ [Z.neg p]) → ∃ l'',
  (l++[Z.neg p+1]) <=[ It f ]=> (l''++[Z.neg p+1]) ∧
  l'' <=[ f ]=> l'.
Proof.
  intros. inv_clean H; all_app_inj_tail.
  assert(p = p0). congruence. subst. eauto.
Qed.

Lemma it_p_rev: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.pos p-1]) <=[ It f ]=> (l'++[Z.pos p-1]).
Proof.
  intros.
  generalize dependent l.
  generalize dependent l'.
  induction p using Pos.peano_ind.
  - intros. destruct (it_p _ _ _ _ H) as (l0 & H0 & H1).
    apply it_0 in H0. subst.
    exists l'. intuition.
  - intros. destruct (it_p _ _ _ _ H) as (l0 & H0 & H1).
    replace (Z.pos (Pos.succ p) - 1) with (Z.pos p) in *; intuition.
    apply IHp in H0. destruct H0 as [l'' [H2 H3]].
    exists l''. intuition.
    eapply E_ItP; eauto.
Qed.

Lemma it_n_rev: ∀ {j} (f : RPP j) l l' p,
  (l ++ [Z.neg p]) <=[ It f ]=> (l' ++ [Z.neg p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.neg p+1]) <=[ It f ]=> (l'++[Z.neg p+1]).
Proof.
  intros.
  generalize dependent l.
  generalize dependent l'.
  induction p using Pos.peano_ind.
  - intros. destruct (it_n _ _ _ _ H) as (l0 & H0 & H1).
    apply it_0 in H0. subst.
    exists l'. intuition.
  - intros. destruct (it_n _ _ _ _ H) as (l0 & H0 & H1).
    replace (Z.neg (Pos.succ p) + 1) with (Z.neg p) in *; intuition.
    apply IHp in H0. destruct H0 as (l'' & H2 & H3).
    exists l''. intuition.
    eapply E_ItN; eauto.
Qed.

Proposition proposition_1_r : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' → l' <=[ inv f ]=> l.
Proof.
  induction f; intros.
  - inv_clean H. intuition.
  - inv_clean H. replace n with (--n) at 2; intuition.
  - inv_clean H. replace n with ((n+1)-1) at 2; intuition.
  - inv_clean H. replace n with ((n-1)+1) at 2; intuition.
  - inv_clean H. intuition.
  - inv_clean H. eapply E_Co; eauto.
  - inv_clean H. eapply E_Pa; eauto.
  - destruct (it_ex _ _ _ H) as (l1 & l1' & n & H1 & H1'). subst.
    generalize dependent l1.
    generalize dependent l1'.
    induction n using Z_pos_ind.
    + intros. apply it_0 in H. rewrite H. constructor.
    + intros. destruct (it_p_rev _ _ _ _ H) as (l' & H0 & H1).
      eapply E_ItP; eauto.
    + intros. destruct (it_n_rev _ _ _ _ H) as (l' & H0 & H1).
      eapply E_ItN; eauto.
  - inv_clean H; [eapply E_IfP | eapply E_IfZ | eapply E_IfN]; eauto.
Qed.

Definition inc := It Su.
Proposition inc_rel : ∀ n m,
  [n; m] <=[inc]=> [n + Z.abs m; m].
Proof.
  intros. unfold inc.
  induction m using Z_pos_ind.
  - rewrite Z.add_0_r. eapply E_ItZ.  eauto. exact (E_ItZ Su [n]).
  - pose( E_Su (n + (Z.abs (Z.pos p - 1))) ).
    replace (n+Z.abs(Z.pos p-1)+1) with (n+Z.abs(Z.pos p)) in r; intuition.
    apply (E_ItP Su p [n] [n+Z.abs(Z.pos p-1)] [n+Z.abs(Z.pos p)]); intuition.
  - pose( E_Su (n + (Z.abs (Z.neg p + 1)))).
    replace (n+Z.abs(Z.neg p+1)+1) with (n+Z.abs(Z.neg p)) in r; intuition.
    apply (E_ItN Su p [n] [n+Z.abs(Z.neg p+1)] [n+Z.abs(Z.neg p)]); intuition.
Qed.

Proposition eq_tail : ∀ {X} (l l' : list X) x,
  l = l' → l ++ [x] = l' ++ [x].
Proof. intros. rewrite H. reflexivity. Qed.

Lemma removelast_last : ∀ {X n d} (l : list X),
  length l = (n + 1)%nat → removelast l ++ [last l d] = l.
Proof.
  intros.
  assert (l ≠ []).
  { intro. assert (length l = O). rewrite H0. 
    reflexivity. intuition. }
  rewrite <-(app_removelast_last d H0). reflexivity.
Qed.

Proposition list_or : ∀ {X} (l : list X),
  l = [] ∨ ∃ l' x, l = l' ++ [x].
Proof.
  intros. destruct l eqn:eqn.
  - left. reflexivity.
  - right.
    assert(l <> []). {rewrite eqn. discriminate. }
    pose (@app_removelast_last _ l x H).
    exists (removelast l).
    exists (last l x). rewrite <- eqn. assumption.
Qed.

Lemma it_0: ∀ {j} (f : RPP j) l l',
  (l ++ [0]) <=[ It f ]=> l' → l' = l ++ [0].
Proof.
  intros. inversion H.
  - reflexivity.
  - apply app_inj_tail in H4. destruct H4.
    assert(n = -1); intuition. rewrite H10 in H5. discriminate.
  - apply app_inj_tail in H4. destruct H4.
    assert(n = 1); intuition. rewrite H10 in H5. discriminate.
Qed.

Lemma absurd_app : ∀ {X} (x : X) (l : list X), l ++ [x] <> [].
Proof.
  unfold not. intros.
  symmetry in H. apply app_cons_not_nil in H.
  assumption.
Qed.

Lemma rel_false : ∀ {j} (f : RPP j) l, [] <=[ f ]=> l → False.
Proof.
  induction f; intros; inversion H;
  try match goal with
    H : ?l ++ [?n] = [] |- _ => apply (absurd_app _ _ H) end.

  - inv_clean H0. inv_clean H1. subst. apply (IHf1 _ H3).
  - inv_clean H5. inv_clean H6. subst.
    apply app_eq_nil in H7. destruct H7. subst. apply (IHf1 _ H8).
Qed.


Proposition proposition_1_r : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' → l' <=[ inv f ]=> l.
Proof.
  induction f; intros.
  - inversion H. constructor.
  - inversion H. replace n with (--n) at 2; intuition. constructor.
  - inversion H. replace n with ((n+1)-1) at 2; intuition. constructor.
  - inversion H. replace n with ((n-1)+1) at 2; intuition. constructor.
  - inversion H. constructor.
  - inversion H. inv_clean H0. inv_clean H1. subst.
    apply IHf1 in H3.
    apply IHf2 in H6.
    apply E_Co with l'0; trivial.
  - inversion H. inv_clean H5. inv_clean H6. subst.
    constructor; intuition.
  - induction contra; try discriminate.

destruct (list_or l).
    + rewrite H0 in H. apply rel_false in H. contradiction.
    + destruct H0 as [l0 [x eqn]]. subst.
      destruct x.
      * apply it_0 in H. rewrite H. apply E_ItZ.
      * induction p using Pos.peano_ind.
        -- inversion H.
          ++ constructor.
          ++ inv_clean H3. subst.



usingZ_nat_ind.
      * inversion H. inv_clean H4. subst.


inversion H. constructor.
  -  inv_clean H3. subst. clear H0 H1.
    induction n using Z_nat_ind.
    + inversion H7.
      * inv_clean H5.
        apply app_inj_tail in H6. assert (l = l0); intuition.
        apply app_inj_tail in H9. assert (l = l'0); intuition.
        subst. clear H1 H2 H4 H10 H11 H12 H13.
        apply IHf in H8.
        pose (E_ItZ (inv f) l'').
        pose (E_ItP (inv f) 0 l'' l'' l'0). simpl in r0.
        apply r0; intuition.
      * assert(n = -1). { apply app_inj_tail in H6. intuition. }
        subst. contradiction.
      * assert(n = 1). { apply app_inj_tail in H6. intuition. }
        subst. contradiction.
    



simpl.

    apply IHf in H8. clear H1 H0.
    


  - admit.
  - inv_clean H4. inv_clean H5. inv_clean H6. subst.
    apply IHf1 in H9.
    constructor; intuition.
  - inv_clean H4. inv_clean H5. inv_clean H6. subst.
    apply IHf2 in H9.
    apply E_IfZ; intuition.
  - inv_clean H4. inv_clean H5. inv_clean H6. subst.
    apply IHf3 in H9.
    apply E_IfN; intuition.

Definition dec := inv inc.
Proposition dec_rel : ∀ n m,
  [n; m] <=[dec]=> [n - (Z.abs m); m].
Proof.
  intros. remember (n - Z.abs m) as n'.
  replace n with (n' + Z.abs m); intuition.
  unfold dec. rewrite proposition_1.
  apply inc_rel.
Qed.