Require Import Unicode.Utf8 List ZArith Lia Permutation.
Import ListNotations.

(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
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

Declare Custom Entry rpp.
Declare Scope rpp_scope.
Notation "<{ e }>" := e
  (at level 0, e custom rpp at level 99) : rpp_scope.
Notation "( x )" := x
  (in custom rpp, x at level 99) : rpp_scope.
Notation "x" := x
  (in custom rpp at level 0, x constr at level 0) : rpp_scope.
Notation "f x .. y" := (.. (f x) .. y)
  (in custom rpp at level 0, only parsing,
  f constr at level 0, x constr at level 9,
  y constr at level 9) : rpp_scope.
Notation "f ; g" := (Co f g)
  (in custom rpp at level 50, right associativity).
Notation "f ‖ g" := (Pa f g)
  (in custom rpp at level 50, right associativity).
Open Scope rpp_scope.

Reserved Notation
  "l '<=[' c ']=>' l'"
  (at level 40, c custom rpp at level 99,
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
<<<<<<< Updated upstream
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
=======
  | E_IfP : ∀ {j} (f g h : RPP j) p l l',
      l <=[ f ]=> l' →
      (l++[Z.pos p]) <=[ If f g h ]=> (l'++[Z.pos p])
  | E_IfZ : ∀ {j} (f g h : RPP j) l l',
      l <=[ g ]=> l' →
      (l++[0]) <=[ If f g h ]=> (l'++[0])
  | E_IfN : ∀ {j} (f g h : RPP j) p l l',
>>>>>>> Stashed changes
      l <=[ h ]=> l' →
      (l++[Z.neg p]) <=[ If f g h ]=> (l'++[Z.neg p])

  where "l <=[ f ]=> l'" := (RPP_rel f l l').

Create HintDb RPP_Db.
#[export] Hint Constructors RPP_rel : RPP_Db.

(* Principio di induzione comodo per It *)
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
  - replace (Z.neg (Pos.succ p)) with (Z.pred (Z.neg p)); intuition.
    replace (Z.neg p) with (Z.succ(Z.pred(Z.neg p))) in IHp; intuition.
    applys H1 IHp.
Qed.

<<<<<<< Updated upstream
Lemma it_ex : ∀ f l l',
=======
(* i prossimi lemmi sono utili per "invertire" It tagliando via le parti inutili *)
Lemma it_ex : ∀ {j} (f : RPP j) l l',
>>>>>>> Stashed changes
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

<<<<<<< Updated upstream
Lemma it_p_rev: ∀ f l l' p,
=======

Ltac inverts_it :=
  match goal with
  | H : ?l <=[ ?f ]=> ?l' |- _ =>
    lets (l1 & l1' & n & H1 & H1') : @it_ex H; subst;
    gen l1 l1';
    induction _ using Z_pos_ind; intros;
    [ lets (H1 & H2) : @it_0 H; subst
    | lets (l' & H0 & H1) : @it_p H
    | lets (l' & H0 & H1) : @it_n H ] end.

Proposition rel_length : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' → length l = length l'.
Proof.
  intros. gen l l'.
  induction f; intros; try (inverts H; reflexivity).
  - inverts H. apply IHf1 in H3. apply IHf2 in H6. intuition.
  - inverts H. repeat rewrite app_length. intuition.
  - inverts_it.
    + reflexivity.
    + apply IHf in H1. apply IHy in H0.
      repeat rewrite app_length in *. intuition.
    + apply IHf in H1. apply IHy in H0.
      repeat rewrite app_length in *. intuition.
  - inverts H;
    match goal with
    | H : _ <=[ _ ]=> _, IHf : _ |- _ => apply IHf in H;
    repeat rewrite app_length; rewrite H; intuition end.
Qed.

Lemma it_p_rev: ∀ {j} (f : RPP j) l l' p,
>>>>>>> Stashed changes
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.pos p-1]) <=[ It f ]=> (l'++[Z.pos p-1]).
Proof.
  intros.
  gen l l'.
  induction p using Pos.peano_ind.
<<<<<<< Updated upstream
  - intros. lets (l0 & H0 & H1) : it_p H.
    apply it_0 in H0. subst.
    exists l'. intuition.
  - intros. lets (l0 & H0 & H1) : it_p H.
=======
  - intros. lets (l0 & H0 & H1) : @it_p H.
    lets (H2 & H3) : @it_0 H0. rewrite <- H2 in *.
    exists l'. split. assumption.
    simpl. constructor. apply rel_length in H1. intuition.
  - intros. lets (l0 & H0 & H1) : @it_p H.
>>>>>>> Stashed changes
    replace (Z.pos (Pos.succ p) - 1) with (Z.pos p) in *; intuition.
    apply IHp in H0. lets (l'' & H2 & H3) : H0.
    exists l''. intuition.
    eapply E_ItP; eauto.
Qed.

<<<<<<< Updated upstream
Lemma it_n_rev: ∀ f l l' p,
=======
Lemma it_n_rev: ∀ {j} (f : RPP j) l l' p,
>>>>>>> Stashed changes
  (l ++ [Z.neg p]) <=[ It f ]=> (l' ++ [Z.neg p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.neg p+1]) <=[ It f ]=> (l'++[Z.neg p+1]).
Proof.
  intros.
  gen l l'.
  induction p using Pos.peano_ind.
  - intros. lets (l0 & H0 & H1) : @it_n H.
    lets (H2 & H3) : @it_0 H0. rewrite <- H2 in *.
    exists l'. split. assumption.
    simpl. constructor. apply rel_length in H1. intuition.
  - intros. lets (l0 & H0 & H1) : @it_n H.
    replace (Z.neg (Pos.succ p) + 1) with (Z.neg p) in *; intuition.
    apply IHp in H0. lets (l'' & H2 & H3) : H0.
    exists l''. intuition.
    eapply E_ItN; eauto.
Qed.

Ltac inverts_it_rev :=
  match goal with
  | H : ?l <=[ ?f ]=> ?l' |- _ =>
    lets (l1 & l1' & n & H1 & H1') : @it_ex H; subst;
    gen l1 l1';
    induction _ using Z_pos_ind; intros;
    [ lets (H1 & H2) : @it_0 H; subst
    | lets (l' & H0 & H1) : @it_p_rev H
    | lets (l' & H0 & H1) : @it_n_rev H ] end.

Proposition proposition_1_r : ∀ {j} (f : RPP j) l l',
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
  - inverts_it_rev.
    + eapply E_ItZ; eauto.
    + eapply E_ItP; eauto.
    + eapply E_ItN; eauto.
  - inverts H; [eapply E_IfP | eapply E_IfZ | eapply E_IfN]; eauto.
Qed.

Proposition proposition_1_l : ∀ {j} (f : RPP j) l l',
  l <=[ inv f ]=> l' → l' <=[ f ]=> l.
Proof.
  intros. rewrite <- double_inverse at 1.
  apply proposition_1_r. assumption.
Qed.

Proposition proposition_1 : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' <-> l' <=[ inv f ]=> l.
Proof. split; [apply proposition_1_r | apply proposition_1_l]. Qed.

Definition inc := It Su.
Proposition inc_rel : ∀ n m,
  [n; m] <=[inc]=> [n + Z.abs m; m].
Proof.
  intros. unfold inc.
  induction m using Z_pos_ind.
  - rewrite Z.add_0_r. applys @E_ItZ Su [n]; intuition.
  - applys @E_ItP [n] [n+Z.abs(Z.pos p-1)] [n+Z.abs(Z.pos p)]; intuition.
    replace (n+Z.abs(Z.pos p)) with (n+Z.abs(Z.pos p-1)+1); intuition.
  - applys @E_ItN [n] [n+Z.abs(Z.neg p+1)] [n+Z.abs(Z.neg p)]; intuition.
    replace (n+Z.abs(Z.neg p)) with (n + Z.abs (Z.neg p + 1)+1); intuition.
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

Fixpoint Id' (n : nat) : RPP n :=
  match n as m0 return (RPP m0) with
    | 0%nat => Nu
    | S m0 => <{ Id ‖ (Id' m0) }>
  end.

Lemma Id'_identity : ∀ l,
  l <=[ Id' (length l) ]=> l.
Proof.
  intros.
  remember (length l) as n. gen l.
  induction n.
  - intros.
    asserts_rewrite(l = []). apply length_zero_iff_nil. auto.
    constructor.
  - intros. simpl.
    destruct l; try discriminate.
    assert(n = length l); intuition.
    applys @E_Pa Id [z] [z] l l; intuition.
Qed.

Proposition RPP_perm : ∀ {l l'} (p : Permutation l l'),
  ∃ (f : RPP (length l)), l <=[ f ]=> l'.
Proof.
  intros.
  induction p.
  - exists Nu. constructor.
  - lets f H : IHp.
    exists <{ Id ‖ f }>.
    pose (E_Id x).
    applys @E_Pa f r H.
  - exists <{ Sw ‖ Id' (length l) }>.
    pose (E_Sw y x).
    pose (Id'_identity l).
    applys @E_Pa Sw [y;x] [x;y] l; intuition.
  - lets f1 H1 : IHp1.
    lets H : @rel_length H1. rewrite <- H in IHp2.
    lets f2 H2 : IHp2.
    exists <{ f1 ; f2 }>.
    eapply @E_Co; eauto.
Qed.

Fixpoint arity {j} (f : RPP j) : nat :=
  match f with
  | Nu => 0
  | Id | Ne | Su | Pr => 1
  | Sw => 2
  | <{ f; g }> => arity f
  | <{ f ‖ g }> => (arity f) + (arity g)
  | It f => S (arity f)
  | If f g h => S (arity f)
  end.

Proposition arity_index : ∀ {j} (f : RPP j),
  arity f = j.
Proof.
  intros. induction f; try simpl; try intuition.
Qed.

Proposition arity_length : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' → length l = arity f.
Proof.
  intros. gen l l'.
  induction f; intros; try (inverts H; eauto; reflexivity).
  - inverts H. rewrite app_length. simpl.
    apply IHf1 in H8. apply IHf2 in H9. auto.
  - inverts_it_rev.
    + simpl. rewrite (arity_index f).
      rewrite app_length. rewrite Nat.add_comm. intuition.
    + apply IHf in H0.
      rewrite app_length. rewrite H0. simpl. intuition. 
    + apply IHf in H0.
      rewrite app_length. rewrite H0. simpl. intuition. 
  - pose (arity_index f1). pose (arity_index f2). pose (arity_index f3).
    inverts H; rewrite app_length;
    match goal with
    | H : _ <=[ _ ]=> _, IH : _ |- _ => apply IH in H; rewrite H end;
    simpl; intuition.
Qed.


Lemma length_Sn_ex : ∀ {X n} {l : list X},
  length l = S n → ∃ l' x, l = l' ++ [x] ∧ length l' = n.
Proof.
  intros.
  assert (l ≠ []).
  { intro. assert (length l = O); intuition.
    rewrite H0. reflexivity. }
  lets (l' & x & eq) : exists_last H0.
  exists l' x.
  split. assumption.
  assert ( length l = S (length l') ).
  { rewrite eq. rewrite app_length.
    rewrite Nat.add_comm. simpl. reflexivity. }
  intuition.
Qed.

Lemma sublist_same_length : ∀ {X} (a b c d : list X),
  a ++ b = c ++ d → length a = length c → a = c ∧ b = d.
Proof.
  intros. assert (a = c).
  - remember (length a) as n.
    symmetry in Heqn. symmetry in H0.
    gen a b c d.
    induction n; intros.
    + rewrite length_zero_iff_nil in *.
      rewrite Heqn. rewrite H0. reflexivity.
    + lets (l & x & Hl & Hx) : @length_Sn_ex Heqn.
      lets (m & y & Hm & Hy) : @length_Sn_ex H0.
      assert (l = m).
      { applys IHn l ([x]++b) m ([y]++d); intuition.
        repeat rewrite app_assoc.
        rewrite <- Hl. rewrite <- Hm. assumption. }
      assert (x = y).
      { subst. repeat rewrite <- app_assoc in H.
        rewrite (app_inv_head_iff m) in H.
        inverts H. reflexivity. }
      subst. reflexivity.
  - split.
    + assumption.
    + rewrite H1 in H. apply app_inv_head in H. assumption.
Qed.

Theorem deterministic : ∀ {j} (f : RPP j) l l0 l1,
     l <=[ f ]=> l0 →
     l <=[ f ]=> l1 →
     l0 = l1.
Proof.
  intros. gen l l0 l1.
  induction f; try (intros; inverts H; inverts H0; reflexivity).
  - intros. inverts H. inverts H0.
    assert (l' = l'0). applys IHf1 H3. auto. subst.
    applys IHf2 H7 H8.
  - intros. inverts H. inverts H0.
    assert(l0 = l3 ∧ l2 = l4).
    { applys @sublist_same_length; auto.
    rewrite (arity_length _ _ _ H9).
    rewrite (arity_length _ _ _ H12).
    reflexivity. }
    lets (H' & H'') : H0. clear H0. subst.
    assert (l1' = l1'0). applys IHf1 H9 H12.
    assert (l2' = l2'0). applys IHf2 H10 H13.
    subst. reflexivity.
  - intros.
    lets (l' & l0' & n & H' & H0') : @it_ex H.
    lets (l'0 & l0'' & n' & H'' & H0'') : @it_ex H0. subst.
    apply app_inj_tail in H''. destruct H''. subst.
    gen l0' l'0 l0''.
    induction n' using Z_pos_ind.
    + intros. subst. apply it_0 in H. apply it_0 in H0.
      intuition. subst. reflexivity.
    + intros.
      lets (a & b & c) : @it_p H.
      lets (a' & b' & c') : @it_p H0.
      pose (IHn' a l'0 b a' b'). apply app_inj_tail in e. destruct e. subst.
      assert(l0' = l0''). applys IHf a' c c'. rewrite H1. reflexivity.
    + intros.
      lets (a & b & c) : @it_n H.
      lets (a' & b' & c') : @it_n H0.
      pose (IHn' a l'0 b a' b'). apply app_inj_tail in e. destruct e. subst.
      assert(l0' = l0''). applys IHf a' c c'. rewrite H1. reflexivity.
  - intros. inverts H.
    + inverts H0; apply app_inj_tail in H10; destruct H10; subst; rewrite H4.
      * assert(l' = l'0). applys IHf1 H9 H11. subst. reflexivity.
      * discriminate.
      * discriminate.
    + inverts H0; apply app_inj_tail in H10; destruct H10.
      * discriminate.
      * subst. assert(l' = l'0). applys IHf2 H9 H11. subst. reflexivity.
      * discriminate.
    + inverts H0; apply app_inj_tail in H10; destruct H10; subst; rewrite H4.
      * discriminate.
      * discriminate.
      * assert(l' = l'0). applys IHf3 H9 H11. subst. reflexivity.
Qed.