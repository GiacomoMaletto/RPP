Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
Require Import LibTactics.
Require Import splice definitions proofs.
Set Implicit Arguments.

Open Scope nat.

Definition dr_step :=
  If (Pr ‖ Su) id (Su ‖ Pr);;
      Sw;; If id (Ne ‖ Su) id;;
      \[2]\;; If id (Su ‖ Ne) id;; \[2;1;0]\.

Definition sh :=
  If id id Sw;;
  id ‖ Pr;;
  Sw;; It Ne;;
  id ‖ (Sw;; It Ne);;
  Id 2 ‖ Pr.

Definition dr :=
  inv (id ‖ sh);;
  It dr_step;;
  id ‖ sh;;
  id ‖ Sw.

Open Scope Z.

Definition alt n x := if Nat.even n then x else -x.

Lemma alt_succ : ∀ n x, alt (S n) x = - alt n x.
Proof.
  intros. unfold alt. destruct (Nat.even n) eqn:eqn.
  - rewrite Nat.even_succ. rewrite <- Nat.negb_even.
    rewrite eqn. reflexivity.
  - rewrite Nat.even_succ. rewrite <- Nat.negb_even.
    rewrite eqn. simpl. lia.
Qed.

Lemma alt_add : ∀ n m x,
  alt (n + m) x = alt n (alt m x).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite !alt_succ. rewrite IHn. reflexivity.
Qed.

Lemma alt_minus : ∀ n x,
  alt n (-x) = - alt n x.
Proof.
  intros. change (-x) with (alt 1 x).
  - rewrite <- alt_add.
    replace (n + 1)%nat with (S n). 2:lia.
    apply alt_succ.
Qed.

Lemma it_ne_def : ∀ n m,
  «It Ne» [↑n; m] = [↑n; alt n m].
Proof.
  intros. rewrite it_def. f_equal. rewrite Nat2Z.id.
  induction n.
  - reflexivity.
  - rewrite alt_succ. rewrite iter_succ. rewrite IHn.
    reflexivity.
Qed.

Lemma dr_step_1 : ∀ n,
  «dr_step» [1; 1; ↑n] = [-1; 0; ↑n + 2].
Proof.
  intros. destruct (↑ n) eqn:eqn.
  - reflexivity.
  - simpl. f_equal. f_equal. f_equal. lia.
  - lia.
Qed.

Lemma dr_step_2 : ∀ p n, (1 < p)%positive →
  «dr_step» [1;Zp p;↑n] = [1;Zp p-1;↑n+1].
Proof.
  intros. unfold dr_step. segment.
  asserts_rewrite (
    « If (Pr ‖ Su) id (Su ‖ Pr) » [1; Zp p; ↑n] =
    [1; Zp p-1; ↑n+1] ).
  { reflexivity. }
  rewrite sw_def.
  asserts_rewrite (
    « If id (Ne ‖ Su) id » [Zp p - 1; 1; ↑n + 1] =
    [Zp p - 1; 1; ↑n + 1] ).
  { rewrite if_def.
    destruct (Zp p - 1) eqn:eqn; try lia. reflexivity. }
  destruct (↑ n + 1) eqn:eqn; try lia. reflexivity.
Qed.

Lemma dr_step_3 : ∀ n,
  «dr_step» [-1;↑n;1] = [1;↑n+2;0].
Proof.
  intros. destruct (↑n) eqn:eqn.
  - reflexivity.
  - simpl. f_equal. f_equal. lia.
  - lia.
Qed.

Lemma dr_step_4 : ∀ n q, (1 < q)%positive →
  «dr_step» [-1;↑n;Zp q] = [-1;↑n+1;Zp q-1].
Proof.
  intros. unfold dr_step. segment.
  asserts_rewrite (
    « If (Pr ‖ Su) id (Su ‖ Pr) » [-1; ↑n; Zp q] =
    [-1; ↑n+1; Zp q -1] ).
  { reflexivity. }
  rewrite sw_def.
  asserts_rewrite (
    « If id (Ne ‖ Su) id » [↑n + 1; -1; Zp q -1] =
    [↑n + 1; -1; Zp q -1] ).
  { rewrite if_def.
    destruct (↑ n + 1) eqn:eqn; try lia. reflexivity. }
  destruct (Zp q - 1) eqn:eqn; try lia. reflexivity.
Qed.

Lemma steps : ∀ n m,
  «sh» («dr_step» («inv sh» [↑n; ↑m; 0])) = «cu_step» [↑n; ↑m; 0].
Proof.
  intros.
  unfold sh. simpl inv. segment.
  asserts_rewrite (
    « Id 2 ‖ Su » [↑ n; ↑ m; 0] =
    [↑ n; ↑ m; 1] ).
  { reflexivity. }
  asserts_rewrite (
    « Id 1 ‖ (It Ne;; Sw) » [↑ n; ↑ m; 1] =
    ↑ n :: «Sw» («It Ne» [↑ m; 1]) ).
  { reflexivity. }
  rewrite it_ne_def.
  asserts_rewrite (
    « Sw » [↑ m; alt m 1] = [alt m 1; ↑ m] ).
  { reflexivity. }
  asserts_rewrite (
    « It Ne » [↑ n; alt m 1; ↑ m] =
    [↑ n; alt (n+m) 1; ↑ m] ).
  { rewrite longer. simpl_splice. rewrite it_ne_def.
    rewrite <- alt_add. auto. }
  asserts_rewrite (
    « Sw » [↑ n; alt (n + m) 1; ↑ m] =
    [alt (n + m) 1; ↑ n; ↑ m] ).
  { reflexivity. }
  asserts_rewrite (
    « Id 1 ‖ Su » [alt (n + m) 1; ↑ n; ↑ m] =
    [alt (n + m) 1; ↑ n + 1; ↑ m] ).
  { reflexivity. }
  destruct (Nat.even (n + m)) eqn:nm_ev.
  - unfold alt. rewrite nm_ev.
    asserts_rewrite (
      « If (Id 1) (Id 1) Sw » [1; ↑ n + 1; ↑ m] =
      [1; ↑ n + 1; ↑ m] ).
    { reflexivity. }
    destruct n.
    + simpl in nm_ev. change (↑ 0 + 1) with 1.
      rewrite dr_step_1.
      asserts_rewrite (
        « If id id Sw » [-1; 0; ↑ m + 2] =
        [-1; ↑ m + 2; 0] ).
      { reflexivity. }
      asserts_rewrite (
        « Sw » (« id ‖ Pr » [-1; ↑ m + 2; 0]) =
        [↑ m + 1; -1; 0] ).
      { simpl. f_equal. lia. }
      asserts_rewrite (
        « It Ne » [↑ m + 1; -1; 0] =
        [↑ m + 1; alt m 1; 0] ).
      { rewrite longer. simpl_splice.
        replace (↑ m + 1) with (↑ (1+m)). 2:lia.
        rewrite it_ne_def. simpl. f_equal. f_equal.
        rewrite !alt_succ. rewrite Z.eq_opp_l.
        apply alt_minus with (n:=m) (x:=1). }
      rewrite cu_step_def. simpl.
      f_equal. lia. f_equal. f_equal. unfold alt.
      rewrite nm_ev. reflexivity.
    + asserts_rewrite (
        « dr_step » [1; ↑ S n + 1; ↑ m] =
        [1; ↑ S n; ↑ m + 1] ).
      { destruct (↑ S n + 1) eqn:eqn; try lia.
        rewrite dr_step_2. 2:lia.
        f_equal. f_equal. lia. }
      remember (S n) as n'.
      asserts_rewrite (
        « If id id Sw » [1; ↑ n'; ↑ m + 1] =
        [1; ↑ n'; ↑ m + 1] ).
      { reflexivity. }
      asserts_rewrite (
        « id ‖ Pr » [1; ↑ n'; ↑ m + 1] =
        [1; ↑ n' - 1; ↑ m + 1] ).
      { reflexivity. }
      rewrite sw_def.
      asserts_rewrite (
        « It Ne » [↑ n' - 1; 1; ↑ m + 1] =
        [↑ n' - 1; - alt n' 1; ↑ m + 1] ).
      { rewrite longer. simpl_splice. rewrite Heqn'.
        replace (↑ S n - 1) with (↑ n). 2:lia.
        rewrite it_ne_def. simpl. f_equal. f_equal.
        rewrite alt_succ. lia. }
      asserts_rewrite (
        « id ‖ (Sw;; It Ne) » [↑ n' - 1; - alt n' 1; ↑ m + 1] =
        ↑ n' - 1 :: «It Ne» [↑ m + 1; - alt n' 1] ).
      { reflexivity. }
      asserts_rewrite (
        « It Ne » [↑ m + 1; - alt n' 1] =
        [↑ m + 1; 1] ).
      { replace (↑ m + 1) with (↑ (1+m)). 2:lia.
        rewrite it_ne_def. f_equal. rewrite alt_minus.
        rewrite <- alt_add. rewrite <- alt_succ. simpl.
        unfold alt. rewrite Nat.even_succ_succ.
        rewrite Nat.add_comm. rewrite nm_ev. reflexivity. }
      rewrite cu_step_def. rewrite Heqn'.
      unfold cu'_fst. unfold cu'_snd.
      asserts_rewrite (
        « Id 2 ‖ Pr » [↑ S n - 1; ↑ m + 1; 1] =
        [↑ S n - 1; ↑ m + 1; 0] ).
      { reflexivity. }
      f_equal. lia. f_equal. lia.
  - unfold alt. rewrite nm_ev. simpl (-(1)).
    asserts_rewrite (
      « If (Id 1) (Id 1) Sw » [-1; ↑ n + 1; ↑ m] =
      [-1; ↑ m; ↑ n + 1] ).
    { reflexivity. }
    destruct n.
    + simpl in nm_ev. change (↑ 0 + 1) with 1.
      rewrite dr_step_3.
      asserts_rewrite (
        « If id id Sw » [1; ↑ m + 2; 0] =
        [1; ↑ m + 2; 0] ).
      { reflexivity. }
      asserts_rewrite (
        « Sw » (« id ‖ Pr » [1; ↑ m + 2; 0]) =
        [↑ m + 1; 1; 0] ).
      { simpl. f_equal. lia. }
      asserts_rewrite (
        « It Ne » [↑ m + 1; 1; 0] =
        [↑ m + 1; 1; 0] ).
      { rewrite longer. simpl_splice.
        replace (↑ m + 1) with (↑ (1+m)). 2:lia.
        rewrite it_ne_def. simpl. f_equal. f_equal.
        rewrite !alt_succ. unfold alt.
        rewrite nm_ev. lia. }
      rewrite cu_step_def. simpl.
      f_equal. lia.
    + asserts_rewrite (
        « dr_step » [-1; ↑ m; ↑ S n + 1] =
        [-1; ↑ m + 1; ↑ S n] ).
      { destruct (↑ S n + 1) eqn:eqn; try lia.
        rewrite dr_step_4. 2:lia.
        f_equal. f_equal. f_equal. lia. }
      remember (S n) as n'.
      asserts_rewrite (
        « If id id Sw » [-1; ↑ m + 1; ↑ n'] =
        [-1; ↑ n'; ↑ m + 1] ).
      { reflexivity. }
      asserts_rewrite (
        « id ‖ Pr » [-1; ↑ n'; ↑ m + 1] =
        [-1; ↑ n' - 1; ↑ m + 1] ).
      { reflexivity. }
      rewrite sw_def.
      asserts_rewrite (
        « It Ne » [↑ n' - 1; -1; ↑ m + 1] =
        [↑ n' - 1; alt n' 1; ↑ m + 1] ).
      { rewrite longer. simpl_splice. rewrite Heqn'.
        replace (↑ S n - 1) with (↑ n). 2:lia.
        rewrite it_ne_def. simpl. f_equal. f_equal.
        rewrite alt_succ.
        change (-1) with (-(1)). apply alt_minus. }
      asserts_rewrite (
        « id ‖ (Sw;; It Ne) » [↑ n' - 1; alt n' 1; ↑ m + 1] =
        ↑ n' - 1 :: «It Ne» [↑ m + 1; alt n' 1] ).
      { reflexivity. }
      asserts_rewrite (
        « It Ne » [↑ m + 1; alt n' 1] =
        [↑ m + 1; 1] ).
      { replace (↑ m + 1) with (↑ (1+m)). 2:lia.
        rewrite it_ne_def. f_equal. f_equal.
        rewrite <- alt_add. simpl. rewrite alt_succ.
        unfold alt. rewrite Nat.add_comm. rewrite nm_ev. lia. }
      rewrite cu_step_def. rewrite Heqn'.
      unfold cu'_fst. unfold cu'_snd.
      asserts_rewrite (
        « Id 2 ‖ Pr » [↑ S n - 1; ↑ m + 1; 1] =
        [↑ S n - 1; ↑ m + 1; 0] ).
      { reflexivity. }
      f_equal. lia. f_equal. lia.
Qed.

Lemma cu_step_ex : ∀ n, ∃ x y, iter « cu_step » n [0; 0; 0] = [↑y; ↑x; 0].
Proof.
  intros. induction n.
  - exists 0%nat 0%nat. reflexivity.
  - destruct IHn as [x [y H]]. rewrite iter_succ.
    rewrite H. rewrite cu_step_def. eauto.
Qed.

Theorem dr_def : ∀ n, «dr» [↑n;0;0;0] = «cu» [↑n;0;0;0].
Proof.
  intros. unfold dr. unfold cu. segment.
  f_equal. simpl (« inv (id ‖ sh) » [↑ n; 0; 0; 0]).
  rewrite !it_def. rewrite !Nat2Z.id.
  asserts_rewrite (
    « id ‖ sh » (↑ n :: iter « dr_step » n [1; 1; 0]) =
    ↑ n :: «sh» (iter «dr_step» n [1;1;0]) ).
  { reflexivity. }
  f_equal. induction n.
  - reflexivity.
  - rewrite !iter_succ. rewrite proposition_1 in *.
    rewrite <- IHn. rewrite <- proposition_1.
    destruct (cu_step_ex n) as [x [y H]].
    rewrite H. apply steps.
Qed.