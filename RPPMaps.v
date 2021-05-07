Require Import Unicode.Utf8 ZArith String Lia.
(* Da Logical Foundations *)
Require Import Maps.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.
Open Scope string_scope.

Inductive com : Type :=
  | CSk
  | CNe (x : string)
  | CSu (x : string)
  | CPr (x : string)
  | CSw (x y : string)
  | CCo (c1 c2 : com)
  | CIt (x : string) (c1 : com)
  | CIf (x : string) (c1 c2 c3 : com).

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e
  (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x
  (in custom com at level 0, x at level 200) : com_scope.
Notation "{ x }" := x
  (in custom com at level 0, x constr at level 98) : com_scope.
Notation "x" := x
  (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x" := (f x)
  (in custom com at level 0, only parsing) : com_scope.
Notation "'skip'" := CSk
  (in custom com at level 0) : com_scope.
Notation "'neg'" := CNe
  (in custom com at level 0) : com_scope.
Notation "'succ'" := CSu
  (in custom com at level 0) : com_scope.
Notation "'pred'" := CPr
  (in custom com at level 0) : com_scope.
Notation "x <=> y" := (CSw x y)
  (in custom com at level 0) : com_scope.
Notation "c1 ; c2" := (CCo c1 c2)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'repeat' x 'do' c1 'end'" := (CIt x c1)
  (in custom com at level 89, x at level 99, c1 at level 99) : com_scope.
Notation "'if' x 'gtz' c1 'eqz' c2 'ltz' c3 'end'" := (CIf x c1 c2 c3)
  (in custom com at level 89, x at level 99,
  c1 at level 99, c2 at level 99, c3 at level 99) : com_scope.


Open Scope com_scope.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".

Check
  <{if X gtz
      repeat Y do succ X end
    eqz skip
    ltz
      repeat Y do pred X end
    end}>.

Fixpoint inv (c : com) : com :=
  match c with
  | CSk => CSk
  | CNe x => CNe x
  | CSu x => CPr x
  | CPr x => CSu x
  | CSw x y => CSw x y
  | CCo c1 c2 => CCo (inv c2) (inv c1)
  | CIt x c1 => CIt x (inv c1)
  | CIf x c1 c2 c3 => CIf x (inv c1) (inv c2) (inv c3)
  end.

Lemma double_inverse : ∀ c, inv (inv c) = c.
Proof. induction c; try constructor; try simpl; congruence. Qed.

Definition varst := total_map bool.
Definition empty_varst : varst := t_empty false.

Open Scope bool_scope.

Definition union_varst (a b : varst) := λ x, (a x) || (b x).
Notation "a ∪ b" := (union_varst a b) (at level 70).

Fixpoint comvarst (c : com) : varst :=
  match c with
  | CSk => empty_varst
  | CNe x => (x!->true; empty_varst)
  | CSu x => (x!->true; empty_varst)
  | CPr x => (x!->true; empty_varst)
  | CSw x y => (y!->true; x!->true; empty_varst)
  | CCo c1 c2 => (comvarst c1) ∪ (comvarst c2)
  | CIt x c1 => (x!->true; comvarst c1)
  | CIf x c1 c2 c3 =>
    (x!->true; (comvarst c1) ∪ (comvarst c2) ∪ (comvarst c3))
  end.

Definition subset_varst (a b : varst) : Prop :=
  ∀ x, a x = true → b x = true.
Notation "a ⊆ b" := (subset_varst a b) (at level 70).

Goal (X!->true; empty_varst) ⊆ (Y!->true; X!->true; empty_varst).
Proof.
  unfold "⊆". intro x.
  destruct (eqb_stringP x X). subst. reflexivity.
  rewrite t_update_neq. discriminate. auto.
Qed.

Notation "a ∈ b" := (b a = true) (at level 70).
Notation "a ∉ b" := (b a = false) (at level 70).

Goal Y ∉ (X!->true; empty_varst).
Proof. reflexivity. Qed.

Definition state := total_map Z.
Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Reserved Notation
  "l '<=[' c ']=>' l'"
  (at level 40, c custom com at level 99,
  l constr, l' constr at next level).

Inductive ceval : com → state → state → Prop :=
  | E_Sk : ∀ st,
      st <=[ skip ]=> st
  | E_Ne : ∀ st x,
      st <=[ neg x ]=> (x !-> - st x ; st)
  | E_Su : ∀ st x,
      st <=[ succ x ]=> (x !-> st x + 1 ; st)
  | E_Pr : ∀ st x,
      st <=[ pred x ]=> (x !-> st x - 1 ; st)
  | E_Sw : ∀ st x y,
      st <=[ x <=> y ]=> (y !-> st x; x !-> st y ; st)
  | E_Co : ∀ st st' st'' c1 c2,
      st <=[ c1 ]=> st' →
      st' <=[ c2 ]=> st'' →
      st <=[ c1 ; c2 ]=> st''

  | E_ItP : ∀ st st' st'' p v c,
      v ∉ comvarst c →
      (v !-> Z.pos p - 1; st) <=[ CIt v c ]=> (v !-> Z.pos p - 1; st') →
      st' <=[ c ]=> st'' →
      (v !-> Z.pos p; st) <=[ CIt v c ]=> (v !-> Z.pos p; st'')

  | E_ItZ : ∀ st c v,
      v ∉ comvarst c →
      (v !-> 0; st) <=[ CIt v c ]=> (v !-> 0; st)

  | E_ItN : ∀ st st' st'' p v c,
      v ∉ comvarst c →
      (v !-> Z.neg p + 1; st) <=[ CIt v c ]=> (v !-> Z.neg p + 1; st') →
      st' <=[ inv c ]=> st'' →
      (v !-> Z.neg p; st) <=[ CIt v c ]=> (v !-> Z.neg p; st'')

  | E_IfP : ∀ st st' p v c1 c2 c3,
      v ∉ comvarst c1 → v ∉ comvarst c2 → v ∉ comvarst c3 →
      st <=[ c1 ]=> st' →
      (v !-> Z.pos p; st) <=[ CIf v c1 c2 c3 ]=> (v !-> Z.pos p; st')

  | E_IfZ : ∀ st st' v c1 c2 c3,
      v ∉ comvarst c1 → v ∉ comvarst c2 → v ∉ comvarst c3 →
      st <=[ c2 ]=> st' →
      (v !-> 0; st) <=[ CIf v c1 c2 c3 ]=> (v !-> 0; st')

  | E_IfN : ∀ st st' p v c1 c2 c3,
      v ∉ comvarst c1 → v ∉ comvarst c2 → v ∉ comvarst c3 →
      st <=[ c3 ]=> st' →
      (v !-> Z.neg p; st) <=[ CIf v c1 c2 c3 ]=> (v !-> Z.neg p; st')

  where "st <=[ c ]=> st'" := (ceval c st st').

Fixpoint is_valid (c : com) : bool :=
  match c with
  | CSk | CNe _ | CSu _ | CPr _ | CSw _ _ => true
  | CCo c1 c2 => is_valid c1 && is_valid c2
  | CIt x c1 => is_valid c1 && negb ((comvarst c1) x)
  | CIf x c1 c2 c3 =>
    is_valid c1 && is_valid c2 && is_valid c3 &&
    negb ((comvarst c1) x) &&
    negb ((comvarst c1) x) &&
    negb ((comvarst c1) x)
  end.

Definition cfun (c : com) (st : state) : state :=
  match c with
  | CSk => st
  | CNe x => (x !-> - st x ; st)
  | CSu x => (x !-> st x + 1 ; st)
  | CPr x => (x !-> st x + 1 ; st)
  | CSw x y => CSw x y
  | CCo c1 c2 => CCo (inv c2) (inv c1)
  | CIt x c1 => CIt x (inv c1)
  | CIf x c1 c2 c3 => CIf x (inv c1) (inv c2) (inv c3)
  end.

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

Lemma eq_func : ∀ A B (f g : A → B) (x : A), f = g → f x = g x.
Proof. intros. f_equal. Qed.

Lemma it_zero : ∀ st st' v c,
  (v !-> 0; st) <=[ repeat v do c end ]=> (v !-> 0; st') →
  st = st'.
Proof.
  intros. inverts H.
  - apply eq_func with (x:=v) in H2.
    rewrite !t_update_eq in H2. discriminate.
  - admit.
  - apply eq_func with (x:=v) in H2.
    rewrite !t_update_eq in H2. discriminate.
Admitted.

Lemma it_sum : ∀ st st' st'' n m v c,
  v ∉ comvarst c →
  (v !-> n; st) <=[ CIt v c ]=> (v !-> n; st') →
  (v !-> m; st') <=[ CIt v c ]=> (v !-> m; st'') →
  (v !-> n+m; st) <=[ CIt v c ]=> (v !-> n+m; st'').
Proof.
  intros. gen st st' st''.
  induction m using Z_pos_ind.
  - intros. inverts H1. replace (n+0) with n; try lia.

Proposition proposition_1_r : ∀ c st st',
  st <=[ c ]=> st' → st' <=[ inv c ]=> st.
Proof.
  induction c; intros.
  - inverts H. simpl. constructor.
  - inversion H. simpl. rewrite H2.
    replace st with (x !-> - st' x; st'). constructor.
    subst. rewrite t_update_eq. rewrite t_update_shadow.
    rewrite Z.opp_involutive. apply t_update_same.
  - inversion H. simpl. rewrite H2.
    replace st with (x !-> st' x - 1; st'). constructor.
    subst. rewrite t_update_eq. rewrite t_update_shadow.
    rewrite Z.add_simpl_r. applys t_update_same.
  - inversion H. simpl. rewrite H2.
    replace st with (x !-> st' x + 1; st'). constructor.
    subst. rewrite t_update_eq. rewrite t_update_shadow.
    rewrite Z.sub_add. applys t_update_same.
  - inversion H. simpl. rewrite H3.
    replace st with (y !-> st' x; x !-> st' y; st'). constructor.
    subst. rewrite t_update_eq.
    destruct (eqb_stringP x y).
    + subst. rewrite t_update_eq. repeat rewrite t_update_same. reflexivity.
    + rewrite t_update_neq; auto. rewrite t_update_eq.
      rewrite t_update_permute; auto. rewrite t_update_shadow.
      rewrite t_update_permute; auto. rewrite t_update_shadow.
      repeat rewrite t_update_same. reflexivity.
  - inverts H. eapply E_Co; eauto.
  - inversion H. simpl. rewrite H4.


  - inverts_it_rev; [eapply E_ItZ | eapply E_ItP | eapply E_ItN ]; eauto.
  - inverts H; [eapply E_IfP | eapply E_IfZ | eapply E_IfN]; eauto.
Qed.









