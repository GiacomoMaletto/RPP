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

Lemma skipn_skipn : ∀ X a b (l : list X),
  skipn a (skipn b l) = skipn (a + b) l.
Proof.
  intros. gen l. induction a.
  - reflexivity.
  - intros. destruct l.
    + rewrite skipn_nil. reflexivity.
    + rewrite skipn_skipn_S.
      change (S a + b) with (S (a + b)).
      rewrite !skipn_cons. auto.
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

Lemma splice_length : ∀ X a b (l : list X),
  length (splice l a b) = min b (length l) - a.
Proof.
  intros. unfold splice.
  rewrite skipn_length. rewrite firstn_length.
  reflexivity.
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

Notation "l ^[ n , m )" := (splice l n m) (at level 10).
Notation "l ^[ n , ∞ )" := (skipn n l) (at level 10).
Notation "l ^[ n ]" := (splice l n (1+n)) (at level 10).