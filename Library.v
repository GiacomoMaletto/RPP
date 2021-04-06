Require Import Unicode.Utf8 List ZArith Lia Permutation.
Import ListNotations.
Require Import Base ListLemmas Ev Rel.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.

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

Proposition inc_rel' : ∀ n m,
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

Notation dec := (inv inc).

Proposition dec_rel : ∀ n m,
  «dec» [n; m] = [n - Z.abs m; m].
Proof.
  intros. remember (n - Z.abs m) as n'.
  assert(n = n' + Z.abs m); intuition.
  rewrite eval_inverse; intuition.
  unfold dec.
  rewrite inc_rel. congruence.
Qed.

Proposition dec_rel' : ∀ n m,
  [n; m] <=[dec]=> [n - (Z.abs m); m].
Proof.
  intros. remember (n - Z.abs m) as n'.
  replace n with (n' + Z.abs m); intuition.
  unfold dec. rewrite proposition_1.
  apply inc_rel'.
Qed.