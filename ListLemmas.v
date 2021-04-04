Require Import Unicode.Utf8 List ZArith.
Require Import LibTactics.
Import ListNotations.

Lemma removelast_length : ∀ [X n] {l : list X},
  length l = n + 1 → length (removelast l) = n.
Proof.
  intros. rewrite removelast_firstn_len.
  rewrite H. simpl. rewrite firstn_length. intuition.
Qed.

Lemma firstn_app_all : ∀ [X n] (l1 l2 : list X),
  length l1 = n → firstn n (l1 ++ l2) = l1.
Proof.
  intros. rewrite firstn_app. rewrite H. rewrite Nat.sub_diag.
  simpl. rewrite <- H. rewrite firstn_all. intuition.
Qed.

Lemma skipn_app_all : ∀ [X n] (l1 l2 : list X),
  length l1 = n → skipn n (l1 ++ l2) = l2.
Proof.
  intros. rewrite skipn_app. rewrite H. rewrite Nat.sub_diag.
  simpl. rewrite <- H. rewrite skipn_all. intuition.
Qed.

Lemma length_Sn_ex : ∀ [X n] {l : list X},
  length l = n + 1 → ∃ l' x, l = l' ++ [x] ∧ length l' = n.
Proof.
  intros.
  assert (l ≠ []).
  { intro. assert (length l = 0). rewrite H0. 
    reflexivity. intuition. }
  destruct (exists_last H0) as [l' [x eq]].
  exists l'. exists x. split. assumption.
  assert (length l = length l' + 1).
  { rewrite eq. rewrite app_length. intuition. }
  intuition.
Qed.

Lemma removelast_Sn : ∀ [X n d] (l : list X),
  length l = n + 1 → removelast l ++ [last l d] = l.
Proof.
  intros.
  assert (l ≠ []).
  { intro. assert (length l = 0). rewrite H0. 
    reflexivity. intuition. }
  rewrite <-(app_removelast_last d H0). reflexivity.
Qed.

Lemma removelast_last : ∀ [X d] (l : list X),
  removelast (l ++ [d]) = l.
Proof.
  intros. rewrite removelast_app.
  - simpl. intuition.
  - discriminate.
Qed.

Lemma eq_tail : ∀ [X] (l l' : list X) x,
  l = l' → l ++ [x] = l' ++ [x].
Proof. intros. rewrite H. reflexivity. Qed.

Lemma sublist_same_length : ∀ [X] (a b c d : list X),
  a ++ b = c ++ d → length a = length c → a = c ∧ b = d.
Proof.
  intros. assert (a = c).
  - remember (length a) as n.
    symmetry in Heqn. symmetry in H0.
    gen a b c d.
    induction n; intros.
    + rewrite length_zero_iff_nil in *.
      rewrite Heqn. rewrite H0. reflexivity.
    + replace (S n) with (n + 1) in *; intuition.
      lets (l & x & Hl & Hx) : @length_Sn_ex Heqn.
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

(*tattica per ottenere una lista concreta a partire ad esempio da length l = 5 *)
Ltac fixedlength l :=
  match goal with H : length l = _ |- _ =>
    repeat (destruct l; try discriminate; injection H as H);
    rewrite length_zero_iff_nil in H end.