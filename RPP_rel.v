Require Import Unicode.Utf8 List ZArith.
Import ListNotations.

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
Proof.
  intros n f. 
  induction f; try constructor; try simpl; congruence.
Qed.


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
  | E_ItP : ∀ {j} (f : RPP j) n l l' l'',
      n > - 1 →
      (l++[n]) <=[ It f ]=> (l'++[n]) →
      l' <=[ f ]=> l'' →
      (l++[n + 1]) <=[ It f ]=> (l''++[n + 1])
  | E_ItN : ∀ {j} (f : RPP j) n l l' l'',
      n < 1 →
      (l++[n]) <=[ It f ]=> (l'++[n]) →
      l' <=[ f ]=> l'' →
      (l++[n - 1]) <=[ It f ]=> (l''++[n - 1])
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

Lemma Z_neg_pos_succ : ∀ p, Z.neg (Pos.succ p) = Z.pred (Z.neg p).
Proof. intuition. Qed.

Proposition Z_nat_ind : ∀ P : Z → Prop, P 0 →
  (∀ x : Z, x >= 0 → P x → P (Z.succ x)) →
  (∀ x : Z, x <= 0 → P x → P (Z.pred x)) →
  ∀ z : Z, P z.
Proof.
  intros. destruct z.
  - assumption.
  - induction p using Pos.peano_ind.
    + apply (H0 0); intuition.
    + rewrite Pos2Z.inj_succ. apply H0; intuition.
  - induction p using Pos.peano_ind.
    + apply (H1 0); intuition.
    + rewrite Z_neg_pos_succ. apply H1; intuition.
Qed.

Definition inc := It Su.
Proposition inc_rel : ∀ n m,
  [n; m] <=[inc]=> [n + Z.abs m; m].
Proof.
  intros. unfold inc. induction m using Z_nat_ind.
  - rewrite Z.add_0_r. exact (E_ItZ Su [n]).
  - pose( E_Su (n + (Z.abs m)) ).
    unfold Z.succ.
    replace (Z.abs (m + 1)) with (Z.abs m + 1); intuition.
    rewrite Z.add_assoc.
    apply (E_ItP Su m [n] [n + Z.abs m] [n + Z.abs m + 1]); intuition.
  - pose( E_Su (n + (Z.abs m)) ).
    unfold Z.pred.
    replace (Z.abs (m + -1)) with (Z.abs m + 1); intuition.
    rewrite Z.add_assoc.
    apply (E_ItN Su m [n] [n + Z.abs m] [n + Z.abs m + 1]); intuition.
Qed.

Ltac inv_clean H :=
  apply inj_pair2_eq_dec in H; trivial; try apply eq_nat_dec.

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
  -

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