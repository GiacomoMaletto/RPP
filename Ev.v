Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
Require Import Base ListLemmas.

Definition build (f : Z → Z) (l : list Z) : list Z :=
  match l with
  | [x] => [f x]
  | _ => l
  end.
Definition evId := build (λ x, x).
Definition evNe := build (λ x, (-x)%Z).
Definition evSu := build (λ x, (x + 1)%Z).
Definition evPr := build (λ x, (x - 1)%Z).

Definition evSw (l : list Z) : list Z :=
  match l with
  | [x;y] => [y;x]
  | _ => l
  end.

Fixpoint power {X : Type} (f : X → X) (n : nat) : X → X :=
  match n with
  | 0 => λ x, x
  | S n => λ x, f (power f n x)
  end.

Fixpoint evaluate {j} (f : RPP j) (l : list Z) : list Z :=
  match f with
  | Nu => l
  | Id => evId l
  | Ne => evNe l
  | Su => evSu l
  | Pr => evPr l
  | Sw => evSw l
  | Co f g => (evaluate g) (evaluate f l)

  | @Pa j _ f g =>
    let (l1, l2) := (firstn j l, skipn j l)
    in (evaluate f l1) ++ (evaluate g l2)

  | It f =>
    let (l1, x) := (removelast l, last l 0%Z)
    in power (evaluate f) (Z.abs_nat x) l1 ++ [x]

  | If f g h =>
    let (l1, x) := (removelast l, last l 0%Z)
    in evaluate (match x with
      | Zpos n => f
      | Z0 => g
      | Zneg n => h
    end) l1 ++ [x]
  end.

(* \laquo f \raquo *)
Notation "« f »" := (evaluate f)
  (f custom rpp) : rpp_scope.

Compute « Ne ‖ Su ‖ Sw » [3;2;5;4]%Z.

Lemma length_evaluate : ∀ {n} (f : RPP n) (l : list Z),
  length l = n → length («f» l) = n.
Proof.
  intros n f. induction f; try do 3 (destruct l; try intuition).
  - intros. simpl. intuition.
  - intros. simpl. rewrite app_length.
    rewrite IHf1. rewrite IHf2. reflexivity.
    rewrite skipn_length. intuition.
    rewrite firstn_length. intuition.
  - intros. simpl. rewrite app_length.
    induction (Z.abs_nat (last l 0%Z)).
    + simpl. rewrite (removelast_length H). reflexivity.
    + simpl.
      assert (length (power («f») n (removelast l)) = j).
      { simpl in IHn. intuition. }
      rewrite (IHf _ H0). reflexivity.
  - intros. simpl. rewrite app_length. simpl.
    destruct (last l 0%Z);
    [ rewrite IHf2 | rewrite IHf1 | rewrite IHf3 ];
    try reflexivity; apply removelast_length; assumption.
Qed.

Lemma ev_comp : ∀ {n} (f g : RPP n) (l : list Z),
  «f ; g» l = «g» («f» l).
Proof. reflexivity. Qed.

Lemma pa_def : ∀ {j k} (f : RPP j) (g : RPP k) (l : list Z),
  «f ‖ g» l = «f» (firstn j l) ++ «g» (skipn j l).
Proof. reflexivity. Qed.

Lemma firstn_pa : ∀ {j k} (f : RPP j) (g : RPP k) {l : list Z},
  length l = j + k →
  firstn j («f ‖ g» l) = «f» (firstn j l).
Proof.
  intros. simpl.
  assert (length («f» (firstn j l)) = j).
  { rewrite length_evaluate. reflexivity.
    rewrite firstn_length. intuition. }
  rewrite (firstn_app_all _ _ H0). reflexivity.
Qed.

Lemma skipn_pa : ∀ {j k} (f : RPP j) (g : RPP k) {l : list Z},
  length l = j + k →
  skipn j («f ‖ g» l) = «g» (skipn j l).
Proof.
  intros. simpl.
  assert (length («f» (firstn j l)) = j).
  { rewrite length_evaluate. reflexivity.
    rewrite firstn_length. intuition. }
  rewrite (skipn_app_all _ _ H0). reflexivity.
Qed.

Theorem proposition_2 : ∀ {j k} {f g : RPP j} {f' g' : RPP k}
  {l : list Z}, length l = j + k →
  « (f ‖ f') ; (g ‖ g') » l = «(f;g) ‖ (f';g')» l.
Proof.
  intros.
  rewrite ev_comp.
  rewrite pa_def.
  rewrite (firstn_pa _ _ H). rewrite (skipn_pa _ _ H).
  reflexivity.
Qed.

Lemma power_S_1 : ∀ {X} (f : X → X) (n : nat) x,
  power f (S n) x = f (power f n x).
Proof. reflexivity. Qed. 

Lemma power_S_2 : ∀ {X} (f : X → X) (n : nat) x,
  power f (S n) x = power f n (f x).
Proof.
  intros X f n. induction n.
  - reflexivity.
  - intro.
    change (power f (S (S n)) x) with (f (power f (S n) x)).
    replace (f (power f (S n) x)) with (f (power f n (f x))).
    change (f (power f n (f x))) with (power f (S n) (f x)).
    reflexivity. rewrite IHn. reflexivity.
Qed.

Lemma length_power : ∀ {n} {f : RPP n} {m} {l : list Z},
  length l = n → length (power «f» m l) = length l.
Proof.
  intros. induction m.
  - reflexivity.
  - simpl. destruct m; rewrite length_evaluate; intuition.
Qed.

Lemma power_inverse : ∀ {n m} {f g : RPP n}
  (h : ∀ l : list Z, length l = n → «g» («f» l) = l)
  (l : list Z), length l = n → power «g» m (power «f» m l) = l.
Proof.
  intros n m f g h. induction m.
  - intuition.
  - intros. rewrite power_S_2. simpl. rewrite h.
    rewrite IHm; intuition. rewrite length_power; intuition.
Qed.

Lemma it_inverse : ∀ {n} {f g : RPP n}
  (h : ∀ l, length l = n → «f;g»l = l),
  ∀ l, length l = n + 1 → «It f;It g»l = l.
Proof.
  intros.
  destruct (length_Sn_ex H) as [l' [x [eq hl]]].
  rewrite eq. simpl.
  repeat rewrite last_last.
  repeat rewrite removelast_last.
  simpl in h.
  rewrite (power_inverse); intuition.
Qed.

Lemma if_co : ∀ {n} (f g h: RPP n) (f' g' h' : RPP n) (l : list Z),
  length l = n + 1 →
  «If f g h;If f' g' h'» l = « If (f ; f') (g;g') (h;h') » l.
Proof.
  intros.
  destruct (length_Sn_ex H) as [l' [x [eq hl]]].
  rewrite eq. simpl.
  repeat rewrite removelast_last.
  repeat rewrite last_last.
  destruct x; intuition.
Qed.

Lemma proposition_1_l : ∀ [n] (f : RPP n) (l : list Z),
  length l = n → «f;inv f» l = l.
Proof.
  intros n f. induction f; intros;
    try (fixedlength l; subst; auto; simpl).
  - rewrite Z.opp_involutive. reflexivity.
  - rewrite Z.add_simpl_r. reflexivity.
  - rewrite Z.sub_add. reflexivity. 
  - intros. simpl in *. rewrite IHf2. rewrite (IHf1 _ H). reflexivity.
    rewrite length_evaluate; intuition.
  - intros. simpl inv. rewrite (proposition_2 H).
    simpl in *. rewrite IHf1. rewrite IHf2. rewrite firstn_skipn.
    reflexivity.
    rewrite skipn_length. intuition.
    rewrite firstn_length. intuition.
  - intros. simpl inv. rewrite it_inverse; intuition.
  - intros. simpl inv. rewrite if_co; auto. simpl.
    destruct (last l 0%Z) eqn:eqn;
      [rewrite IHf2 | rewrite IHf1 | rewrite IHf3 ]; try rewrite <- eqn;
      try (rewrite (removelast_Sn l H); reflexivity);
      rewrite (removelast_length H); reflexivity.
Qed.

Lemma proposition_1_r : ∀ {n} (f : RPP n) (l : list Z),
  length l = n → «inv f;f» l = l.
Proof.
  intros.
  replace «inv f;f» with «inv f; inv(inv f)».
  rewrite proposition_1_l; intuition.
  rewrite double_inverse. reflexivity.
Qed.

Theorem proposition_1 : ∀ {n} (f : RPP n) (l : list Z),
  length l = n → «f;inv f» l = l ∧ «inv f;f» l = l.
Proof.
  intros. split.
  - exact (proposition_1_l f l H).
  - exact (proposition_1_r f l H).
Qed.

Open Scope Z_scope.

Notation inc := <{ It Su }>.
Proposition inc_rel : ∀ n m,
  «inc» [n; m] = [n + Z.abs m; m].
Proof.
  intros. simpl.
  change ([n + Z.abs m; m]) with ([n + Z.abs m] ++ [m]).
  apply eq_tail.
  rewrite <- Zabs2Nat.id_abs. generalize (Z.abs_nat m).
  induction n0.
  - simpl. rewrite <- Zplus_0_r_reverse. reflexivity.
  - simpl. rewrite Zpos_P_of_succ_nat.
    rewrite IHn0. simpl. unfold Z.succ.
    rewrite Z.add_assoc. reflexivity.
Qed.

Proposition eval_inverse : ∀ {j} (f : RPP j) l l',
  length l = j → length l' = j →
  «f» l = l' <-> l = «inv f» l'. 
Proof.
  split.
  - intro.
    apply (f_equal «inv f» ) in H1.
    rewrite <- ev_comp in H1.
    rewrite proposition_1_l in H1; intuition.
  - intro.
    apply (f_equal «f» ) in H1.
    rewrite <- ev_comp in H1.
    rewrite proposition_1_r in H1; intuition.
Qed.

Definition dec := inv inc.
Proposition dec_rel : ∀ n m,
  «dec» [n; m] = [n - Z.abs m; m].
Proof.
  intros. remember (n - Z.abs m) as n'.
  assert(n = n' + Z.abs m); intuition.
  rewrite eval_inverse; intuition.
  unfold dec.
  rewrite double_inverse.
  rewrite inc_rel. congruence.
Qed.