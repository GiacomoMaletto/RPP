Require Import Unicode.Utf8 List Lia.
Import ListNotations.
Require Import LibTactics.
Set Implicit Arguments.

Definition splice X (l : list X) n m := skipn n (firstn m l).

Lemma firstn_splice : ∀ X a b c (l : list X), b ≤ c →
  splice l a b = firstn (b - a) (splice l a c).
Proof.
  intros. unfold splice. rewrite !skipn_firstn_comm.
  rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma skipn_skipn_S : ∀ X a b (l : list X),
  skipn (S a) (skipn b l) = skipn a (skipn (S b) l).
Proof.
  intros. gen a b. induction l.
  - intros. rewrite !skipn_nil. reflexivity.
  - intros. destruct b.
    + reflexivity.
    + rewrite !skipn_cons. auto.
Qed.

Lemma skipn_Sn : ∀ X n (l : list X), skipn (S n) l = tl (skipn n l).
Proof.
  intros. gen l. induction n.
  - reflexivity.
  - intros. destruct l.
    + reflexivity.
    + rewrite skipn_cons. rewrite IHn. reflexivity.
Qed.

Lemma skipn_skipn : ∀ X a b (l : list X),
  skipn a (skipn b l) = skipn (a + b) l.
Proof.
  intros. gen l. induction a.
  - reflexivity.
  - intros. change (S a + b) with (S (a + b)).
    rewrite !skipn_Sn. rewrite IHa. reflexivity.
Qed.

Lemma skipn_splice : ∀ X a b c (l : list X), a ≤ b →
  splice l b c = skipn (b - a) (splice l a c).
Proof.
  intros. unfold splice. rewrite skipn_skipn.
   f_equal. lia.
Qed.

Lemma app_splice : ∀ X a b c (l : list X), a ≤ b → b ≤ c →
  splice l a b ++ splice l b c = splice l a c.
Proof.
  intros.
  rewrite <- (firstn_skipn (b-a) (splice l a c)).
  rewrite firstn_splice with (c:=c). f_equal.
  rewrite skipn_splice with (a:=a). reflexivity.
  assumption. assumption.
Qed.

Lemma app_splice' : ∀ X a b c d (l : list X), a ≤ b → c ≤ d → b = c →
  splice l a b ++ splice l c d = splice l a d.
Proof.
  intros. rewrite H1. apply app_splice. all: lia.
Qed.

Lemma splice_skipn : ∀ X a (l : list X),
  skipn a l = splice l a (length l).
Proof.
  intros. unfold splice. rewrite firstn_all. reflexivity.
Qed.

Lemma splice_app_skipn : ∀ X a b (l : list X), a ≤ b →
  splice l a b ++ skipn b l = skipn a l.
Proof.
  intros. destruct (PeanoNat.Nat.le_ge_cases b (length l)).
  - rewrite !splice_skipn. apply app_splice.
    assumption. assumption.
  - unfold splice. rewrite firstn_all2.
    rewrite <- app_nil_r. f_equal. rewrite skipn_all2.
    reflexivity. assumption. assumption.
Qed.

Lemma splice_app_skipn' : ∀ X a b c (l : list X), a ≤ b → b = c →
  splice l a b ++ skipn c l = skipn a l.
Proof.
  intros. subst. apply splice_app_skipn. easy.
Qed.

Lemma splice_comp : ∀ X a b c d (l : list X),
  splice (splice l a b) c d = splice l (a+c) (min (a+d) b).
Proof.
  intros. unfold splice.
  rewrite firstn_skipn_comm. rewrite skipn_skipn.
  rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma splice_comp_skipn : ∀ X a b c (l : list X),
  skipn c (splice l a b) = splice l (a+c) b.
Proof.
  intros. unfold splice.
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma skipn_comp_splice : ∀ X a b c (l : list X),
  splice (skipn a l) b c = splice l (a+b) (a+c).
Proof.
  intros. unfold splice.
  rewrite firstn_skipn_comm. rewrite skipn_skipn.
  f_equal. lia.
Qed.

Lemma splice_length : ∀ X a b (l : list X),
  length (splice l a b) = min b (length l) - a.
Proof.
  intros. unfold splice.
  rewrite skipn_length. rewrite firstn_length.
  reflexivity.
Qed.

Lemma nth_skipn : ∀ X a (l : list X) d,
  nth a l d = hd d (skipn a l).
Proof.
  intros. destruct (PeanoNat.Nat.le_gt_cases (length l) a).
  - rewrite nth_overflow. rewrite skipn_all2. reflexivity.
    lia. lia.
  - gen l. induction a.
    + destruct l; reflexivity.
    + destruct l. reflexivity.
      simpl. intros. rewrite IHa.
      reflexivity. lia.
Qed.

Lemma nth_splice : ∀ X a (l : list X) d,
  nth a l d = hd d (splice l a (1+a)).
Proof.
  intros. destruct (PeanoNat.Nat.le_gt_cases (length l) a).
  - rewrite nth_overflow. unfold splice.
    rewrite skipn_all2. reflexivity. rewrite firstn_length.
    lia. lia.
  - gen l. induction a.
    + destruct l; reflexivity.
    + destruct l. reflexivity.
      simpl. intros. rewrite IHa.
      reflexivity. lia.
Qed.

Lemma splice_nth : ∀ X a (l : list X) d, a < length l →
  splice l a (1+a) = [nth a l d].
Proof.
  intros. rewrite nth_splice. destruct (splice l a (1 + a)) eqn:eqn.
  - assert(length (splice l a (1+a)) = 0). rewrite eqn. reflexivity.
    rewrite splice_length in H0. lia.
  - destruct l0.
    + reflexivity.
    + assert(2 ≤ length (splice l a (1+a))). rewrite eqn. simpl. lia.
      rewrite splice_length in H0. lia.
Qed.

Lemma splice_nil : ∀ X a b,
  @splice X [] a b = [].
Proof.
  intros. unfold splice.
  rewrite firstn_nil. rewrite skipn_nil. reflexivity.
Qed.

Lemma splice_all : ∀ X a (l : list X), length l ≤ a →
  splice l 0 a = l.
Proof.
  intros. unfold splice. simpl. apply firstn_all2.
  assumption.
Qed.

Lemma splice_all2 : ∀ X a b (l : list X), length l ≤ a →
  splice l a b = [].
Proof.
  intros. unfold splice. apply skipn_all2.
  rewrite firstn_length. lia.
Qed.

Lemma splice_app : ∀ X a b (l l' : list X),
  splice (l++l') a b = splice l a b ++ splice l' (a-length l) (b-length l).
Proof.
  intros. unfold splice. rewrite firstn_app. rewrite skipn_app.
  f_equal. destruct (PeanoNat.Nat.le_gt_cases (length l) b).
  - repeat f_equal. apply firstn_all2. assumption.
  - rewrite !skipn_all2. reflexivity.
    rewrite !firstn_length. lia.
    rewrite !firstn_length. lia.
Qed.

Lemma splice_cons : ∀ X a (x : X) l,
  splice (x::l) 0 (S a) = x :: splice l 0 a.
Proof. reflexivity. Qed.

Lemma firstn_eq_splice : ∀ X a (l : list X),
  firstn a l = splice l 0 a.
Proof. reflexivity. Qed.

Lemma splice_same : ∀ X a (l : list X), splice l a a = [].
Proof.
  intros. unfold splice. rewrite skipn_all2.
  reflexivity. rewrite firstn_length. lia.
Qed.

Lemma splice_same' : ∀ X a b (l : list X), a = b → splice l a b = [].
Proof.
  intros. rewrite H. apply splice_same.
Qed.

Lemma splice_gt : ∀ X a b (l : list X), b ≤ a → splice l a b = [].
Proof.
  intros. unfold splice. rewrite skipn_all2.
  reflexivity. rewrite firstn_length. lia.
Qed.

Lemma splice_gt' : ∀ X a b (l l' : list X), b ≤ a → l ++ splice l' a b = l.
Proof.
  intros. rewrite splice_gt. rewrite app_nil_r. reflexivity. easy.
Qed.

Lemma splice_gt'' : ∀ X a b c (l l' : list X), b ≤ a →
  splice l a b ++ skipn c l' = skipn c l'.
Proof.
  intros. rewrite splice_gt. reflexivity. easy.
Qed.

Lemma map_firstn : ∀ X Y (f : X → Y) n l,
  firstn n (map f l) = map f (firstn n l).
Proof.
  intros. gen n. induction l.
  - intros. rewrite !firstn_nil. reflexivity.
  - intros. destruct n.
    + reflexivity.
    + simpl. rewrite IHl. reflexivity.
Qed.

Lemma map_skipn : ∀ X Y (f : X → Y) n l,
  skipn n (map f l) = map f (skipn n l).
Proof.
  intros. gen n. induction l.
  - intros. rewrite !skipn_nil. reflexivity.
  - intros. destruct n.
    + reflexivity.
    + simpl. rewrite IHl. reflexivity.
Qed.

Lemma map_splice : ∀ X Y (f : X → Y) l a b,
  splice (map f l) a b = map f (splice l a b).
Proof.
  intros. unfold splice.
  rewrite map_firstn. rewrite map_skipn.
  reflexivity.
Qed.

Lemma in_firstn : ∀ X (x : X) n l, In x (firstn n l) → In x l.
Proof.
  intros. gen n. induction l.
  - intros. rewrite firstn_nil in H. simpl in H. false.
  - intros. simpl. destruct n. simpl in H. false.
    simpl in H. destruct H.
    + left. easy.
    + right. apply IHl with (n:=n). easy.
Qed.

Lemma in_skipn : ∀ X (x : X) n l, In x (skipn n l) → In x l.
Proof.
  intros. gen n. induction l.
  - intros. rewrite skipn_nil in H. simpl in H. false.
  - intros. simpl. destruct n. simpl in H. easy.
    simpl in H. right. apply IHl with (n:=n). easy.
Qed.

Lemma repeat_firstn : ∀ X (x : X) n a,
  firstn a (repeat x n) = repeat x (min n a).
Proof.
  intros.
  asserts_rewrite (min n a = length (firstn a (repeat x n))).
  { rewrite firstn_length. rewrite repeat_length. lia. }
  rewrite Forall_eq_repeat with (l:=firstn a (repeat x n))(x:=x).
  f_equal. rewrite firstn_length. rewrite !repeat_length. easy.
  rewrite Forall_forall. intros.
  rewrite repeat_spec with (n:=n) (x:=x). easy.
  apply in_firstn with (n:=a). easy.
Qed.

Lemma repeat_skipn : ∀ X (x : X) n a,
  skipn a (repeat x n) = repeat x (n - a).
Proof.
  intros.
  asserts_rewrite (n - a = length (skipn a (repeat x n))).
  { rewrite skipn_length. rewrite repeat_length. easy. }
  rewrite Forall_eq_repeat with (l:=skipn a (repeat x n))(x:=x).
  f_equal. rewrite skipn_length. rewrite !repeat_length. easy.
  rewrite Forall_forall. intros.
  rewrite repeat_spec with (n:=n) (x:=x). easy.
  apply in_skipn with (n:=a). easy.
Qed.

Lemma repeat_splice : ∀ X (x : X) n a b,
  splice (repeat x n) a b = repeat x (min n b - a).
Proof.
  intros. unfold splice.
  rewrite repeat_firstn. rewrite repeat_skipn. easy.
Qed.

Notation "l ^[ n , m ]" := (splice l n m) (at level 10).
Notation "l ^[ n , ∞ ]" := (skipn n l) (at level 10).
Notation "l ^[ n ]" := (splice l n (1+n)) (at level 10).