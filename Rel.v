Require Import Unicode.Utf8 List ZArith Lia Permutation.
Import ListNotations.
Require Import Base ListLemmas Ev.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.

Open Scope Z_scope.

Reserved Notation
  "l '<=[' c ']=>' l'"
  (at level 40, c custom rpp at level 99,
  l constr, l' constr at next level).

Inductive RPP_rel : ∀ {j}, RPP j → list Z → list Z → Prop :=
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
  | E_Co : ∀ {j} (f g : RPP j) l l' l'',
      l <=[ f ]=> l' →
      l' <=[ g ]=> l'' →
      l <=[ f ; g ]=> l''
  | E_Pa : ∀ {j k} (f : RPP j) (g : RPP k) l1 l1' l2 l2',
      l1 <=[ f ]=> l1' →
      l2 <=[ g ]=> l2' →
      (l1++l2) <=[ f ‖ g ]=> (l1'++l2')
  | E_ItZ : ∀ {j} (f : RPP j) l,
      length l = j →
      (l++[0]) <=[ It f ]=> (l++[0])
  | E_ItP : ∀ {j} (f : RPP j) p l l' l'',
      (l ++ [Z.pos p - 1]) <=[ It f ]=> (l' ++ [Z.pos p - 1]) →
      l' <=[ f ]=> l'' →
      (l ++ [Z.pos p]) <=[ It f ]=> (l'' ++ [Z.pos p])
  | E_ItN : ∀ {j} (f : RPP j) p l l' l'',
      (l ++ [Z.neg p + 1]) <=[ It f ]=> (l' ++ [Z.neg p + 1]) →
      l' <=[ f ]=> l'' →
      (l ++ [Z.neg p]) <=[ It f ]=> (l'' ++ [Z.neg p])
  | E_IfP : ∀ {j} (f g h : RPP j) p l l',
      l <=[ f ]=> l' →
      (l++[Z.pos p]) <=[ If f g h ]=> (l'++[Z.pos p])
  | E_IfZ : ∀ {j} (f g h : RPP j) l l',
      l <=[ g ]=> l' →
      (l++[0]) <=[ If f g h ]=> (l'++[0])
  | E_IfN : ∀ {j} (f g h : RPP j) p l l',
      l <=[ h ]=> l' →
      (l++[Z.neg p]) <=[ If f g h ]=> (l'++[Z.neg p])

  where "l <=[ f ]=> l'" := (RPP_rel f l l').

#[export] Hint Constructors RPP_rel : rpp.

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

(* i prossimi lemmi sono utili per "invertire" It tagliando via le parti inutili *)
Lemma it_ex : ∀ {j} (f : RPP j) l l',
  l <=[ It f ]=> l' → ∃ l1 l1' x,
  l = l1 ++ [x] ∧ l' = l1' ++ [x].
Proof. intros. inverts keep H; eauto. Qed.

Lemma if_ex : ∀ {j} (f g h : RPP j) l l',
  l <=[ If f g h]=> l' → ∃ l1 l1' x,
  l = l1 ++ [x] ∧ l' = l1' ++ [x].
Proof. intros. inverts keep H; eauto. Qed.

Ltac all_app_inj_tail := 
  repeat match goal with
  | H : _ |- _ => apply app_inj_tail in H; destruct H end;
  try congruence.

Lemma it_0: ∀ {j} (f : RPP j) l l',
  (l ++ [0]) <=[ It f ]=> (l' ++ [0]) → l = l' ∧ length l = j.
Proof. intros. split; inverts H; all_app_inj_tail. Qed.

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
  (l ++ [Z.pos p]) <=[ It f ]=> (l' ++ [Z.pos p]) → ∃ l'',
  l <=[ f ]=> l'' ∧
  (l''++[Z.pos p-1]) <=[ It f ]=> (l'++[Z.pos p-1]).
Proof.
  intros.
  gen l l'.
  induction p using Pos.peano_ind.
  - intros. lets (l0 & H0 & H1) : @it_p H.
    lets (H2 & H3) : @it_0 H0. rewrite <- H2 in *.
    exists l'. split. assumption.
    simpl. constructor. apply rel_length in H1. intuition.
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
  - inverts_it_rev; [eapply E_ItZ | eapply E_ItP | eapply E_ItN ]; eauto.
  - inverts H; [eapply E_IfP | eapply E_IfZ | eapply E_IfN]; eauto.
Qed.

Proposition proposition_1_l : ∀ {j} (f : RPP j) l l',
  l <=[ inv f ]=> l' → l' <=[ f ]=> l.
Proof.
  intros. rewrite <- double_inverse at 1.
  apply proposition_1_r. assumption.
Qed.

Proposition proposition_1 : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' ↔ l' <=[ inv f ]=> l.
Proof. split; [apply proposition_1_r | apply proposition_1_l]. Qed.

Proposition inc_rel : ∀ n m,
  [n; m] <=[inc]=> [n + Z.abs m; m].
Proof.
  intros.
  induction m using Z_pos_ind.
  - rewrite Z.add_0_r. applys @E_ItZ Su [n]; intuition.
  - applys @E_ItP [n] [n+Z.abs(Z.pos p-1)] [n+Z.abs(Z.pos p)]; intuition.
    replace (n+Z.abs(Z.pos p)) with (n+Z.abs(Z.pos p-1)+1); intuition.
  - applys @E_ItN [n] [n+Z.abs(Z.neg p+1)] [n+Z.abs(Z.neg p)]; intuition.
    replace (n+Z.abs(Z.neg p)) with (n + Z.abs (Z.neg p + 1)+1); intuition.
Qed.

Proposition dec_rel : ∀ n m,
  [n; m] <=[dec]=> [n - (Z.abs m); m].
Proof.
  intros. remember (n - Z.abs m) as n'.
  replace n with (n' + Z.abs m); intuition.
  unfold dec. rewrite proposition_1.
  apply inc_rel.
Qed.

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

Proposition index_length : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' → length l = j.
Proof.
  intros.
  apply arity_length in H.
  rewrite arity_index in H.
  assumption.
Qed.

Open Scope nat_scope.

Ltac last_rmlast := rewrite last_last in *; rewrite removelast_last in *.

Theorem rel_ev : ∀ {j} (f : RPP j) l l',
  length l = j → («f» l = l') → l <=[ f ]=> l'.
Proof.
  intros. gen l l'. induction f; intros;
  try (fixedlength l; subst; constructor).
  - applys @E_Co; auto using length_evaluate.
  - replace l with ( (firstn j l) ++ (skipn j l) ); try apply firstn_skipn.
    simpl in H0. rewrite <- H0.
    applys @E_Pa.
    applys IHf1. rewrite firstn_length_le; lia. reflexivity.
    applys IHf2. rewrite skipn_length; lia. reflexivity.
  - lets (l0 & x & c & d) : @length_Sn_ex H.
    rewrite c in H0. simpl in H0. last_rmlast. subst.
    remember (Z.abs_nat x) as n. gen l0 x.
    induction n.
    + intros. asserts_rewrite (x = 0%Z); try lia. constructor. auto.
    + intros. simpl. destruct x.
      * discriminate.
      * applys @E_ItP.
        applys IHn IHf. rewrite app_length. reflexivity. lia.
        applys IHf; try apply length_power; reflexivity.
      * applys @E_ItN.
        applys IHn IHf. rewrite app_length. reflexivity. lia.
        applys IHf; try apply length_power; reflexivity.
  - lets (l0 & x & c & d) : @length_Sn_ex H. subst.
    destruct x; simpl; last_rmlast; constructor; eauto.
Qed.

Theorem ev_rel : ∀ {j} (f : RPP j) l l',
  l <=[ f ]=> l' → «f» l = l'.
Proof.
  intros. gen l l'.
  induction f;
  try (intros; inverts H; reflexivity).
  - intros. inverts H.
    apply IHf1 in H3. apply IHf2 in H6.
    simpl. rewrite H3. rewrite H6. reflexivity.
  - intros. inverts H. clear H0 H1. simpl.
    pose (index_length _ _ _ H8) as Hl.
    asserts_rewrite (firstn j (l1 ++ l2) = l1). applys firstn_app_all; auto.
    asserts_rewrite (skipn j (l1 ++ l2) = l2). applys skipn_app_all; auto.
    clear Hl.
    apply IHf1 in H8. apply IHf2 in H9. subst. reflexivity.
  - intros. inverts_it.
    + simpl. last_rmlast. reflexivity.
    + simpl. apply IHf in H1.
      apply IHy in H0. unfold evaluate in H0. fold @evaluate in H0.
      last_rmlast.
      rewrite app_inv_tail_iff in H0.
      rewrite app_inj_tail_iff; intuition.
      replace (Z.abs_nat (Z.pos p)) with (S(Z.abs_nat (Z.pos p - 1))); try lia.
      rewrite power_S_1. rewrite H0. rewrite H1. reflexivity.
    + simpl. apply IHf in H1.
      apply IHy in H0. unfold evaluate in H0. fold @evaluate in H0.
      last_rmlast.
      rewrite app_inv_tail_iff in H0.
      rewrite app_inj_tail_iff; intuition.
      replace (Z.abs_nat (Z.neg p)) with (S(Z.abs_nat (Z.neg p + 1))); try lia.
      rewrite power_S_1. rewrite H0. rewrite H1. reflexivity.
  - intros. inverts H;
    simpl; last_rmlast; rewrite app_inj_tail_iff; intuition.
Qed.

Theorem determininistic : ∀ {j} (f : RPP j) l l0 l1,
  l <=[ f ]=> l0 →
  l <=[ f ]=> l1 →
  l0 = l1.
Proof.
  intros.
  pose (index_length _ _ _ H) as Hl.
  pose (ev_rel f l l0 H).
  pose (ev_rel f l l1 H0).
  rewrite <- e. rewrite <- e0. reflexivity.
Qed.

Theorem ev_rel' : ∀ {j} (f : RPP j) l,
  length l = j → l <=[ f ]=> «f» l.
Proof. intros. applys @rel_ev H @eq_refl. Qed.