Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.
Require Import splice definitions.
Set Implicit Arguments.

(* Nota: i seguenti lemmi sono ovvi ma servono per poter permettere una riscrittura "controllata" dei goal. *)

Lemma id_def : ∀ n l, «Id n» l = l.
Proof. reflexivity. Qed.

Lemma su_def : ∀ n l, «Su» (n :: l) = n + 1 :: l.
Proof. reflexivity. Qed.

Lemma sw_def : ∀ l, «Sw» l =
  match l with x::y::l' => y::x::l' | _=>l end.
Proof. reflexivity. Qed.

Lemma co_def : ∀ f g l, «f;;g» l = «g» («f» l).
Proof. reflexivity. Qed.

Lemma pa_def : ∀ f g l,
  «f ‖ g» l = «f» (l^[0, arity f]) ++ «g» (l^[arity f, ∞]).
Proof. reflexivity. Qed.

Lemma if_def : ∀ f g h l, «If f g h» l =
  match l with []=>[]
  | x::l' => match x with
    | Zpos _ => x::evaluate f l'
    | Z0 => x::evaluate g l'
    | Zneg _ => x::evaluate h l'
    end
  end.
Proof. reflexivity. Qed.

Lemma it_def : ∀ f l, «It f» l =
  match l with []=>[]
  | x::l' => x::iter (evaluate f) (Z.to_nat x) l'
  end.
Proof. reflexivity. Qed.

Lemma ev_it : ∀ f x y, «It f» (x::y) = x :: iter «f» (Z.to_nat x) y.
Proof. reflexivity. Qed.

Lemma inv_involute : ∀ f, inv (inv f) = f.
Proof. induction f; try constructor; simpl; congruence. Qed.

Lemma arity_inv : ∀  f, arity (inv f) = arity f.
Proof.
  induction f.
  simpl. reflexivity.
  all: try (simpl; reflexivity).
  simpl. rewrite IHf1. rewrite IHf2. lia.
  all: try (simpl; lia).
Qed.


Lemma evaluate_nil : ∀ f, «f» [] = [].
Proof.
  induction f; try reflexivity.
  - simpl. congruence.
  - simpl. rewrite splice_nil. rewrite skipn_nil.
    rewrite IHf1. rewrite IHf2. reflexivity.
Qed.

(* Nota: tattica utile per il caso l=[] *)

Ltac nil_case l := destruct l;
  try rewrite !evaluate_nil; try reflexivity.

Lemma length_evaluate : ∀ f l, length («f» l) = length l.
Proof.
  intros. gen l.
  induction f; try nil_case l; intros.
  - nil_case l.
  - simpl. rewrite IHf2. rewrite IHf1. reflexivity.
  - simpl. rewrite app_length.
    rewrite IHf1. rewrite IHf2.
    rewrite <- app_length.
    rewrite splice_app_skipn. reflexivity. lia.
  - simpl. induction (Z.to_nat z); auto. simpl. rewrite IHf; lia.
  - destruct z; simpl; congruence.
Qed.

(* Nota: nella proposizione 2 non c'è alcuna ipotesi sulla lunghezza di l. *)

(* Nota: la tattica liast è stata sviluppata per risolvere goals che necessitano di qualche fatto sulle liste più un'applicazione di lia. *)

Ltac liast := simpl in *;
  try rewrite !evaluate_nil; try rewrite !app_nil_r;
  try rewrite !app_length; try rewrite !length_evaluate;
  try rewrite !splice_length; try rewrite !skipn_length;
  try lia; try reflexivity.

Open Scope nat.
Theorem proposition_2 : ∀ f g f' g' l, arity f = arity g →
  «f‖f';;g‖g'» l = «(f;;g)‖(f';;g')» l.
Proof.
  intros. rewrite co_def. rewrite !pa_def.
  rewrite <- H.
  destruct (Nat.le_ge_cases (length l) (arity f)).
  - rewrite !splice_all. rewrite !skipn_all2.
    all: liast.
  - rewrite splice_app. rewrite skipn_app. liast.
    rewrite <- H. rewrite Nat.max_id. rewrite min_l.
    replace (arity f - (arity f - 0)) with 0.
    f_equal. all: liast.
    + rewrite splice_all. unfold splice. all: liast.
    + f_equal. rewrite skipn_all2. all: liast.
Qed.


Lemma iter_succ : ∀ X (f : X → X) n x,
  iter f (S n) x = f (iter f n x).
Proof. reflexivity. Qed.

Lemma iter_succ_r : ∀ X (f : X → X) n x,
  iter f (S n) x = iter f n (f x).
Proof.
  intros. induction n.
  - reflexivity.
  - rewrite iter_succ. rewrite IHn. reflexivity.
Qed.

Lemma iter_comm : ∀ X (f g : X → X), (∀ x, f (g x) = g (f x)) →
  ∀ n x, f (iter g n x) = iter g n (f x).
Proof.
  intros. induction n. reflexivity.
  rewrite iter_succ. rewrite H. rewrite IHn. reflexivity.
Qed.

Lemma iter_inverse : ∀ X (f g : X → X), (∀ x, f (g x) = x) →
  ∀ n x, iter f n (iter g n x) = x.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite iter_comm; auto. rewrite H. assumption.
Qed.

Lemma co_if : ∀ f g h f' g' h' l,
  «If f g h;;If f' g' h'» l = «If (f;;f') (g;;g') (h;;h') » l.
Proof.
  intros. nil_case l.
  simpl. destruct z; reflexivity.
Qed.

Theorem proposition_1_l_co : ∀ f l, «f;;inv f» l = l.
Proof.
  intros. gen l. induction f; try (nil_case l; simpl; f_equal; lia).
  - nil_case l. nil_case l.
  - intros. simpl in *. congruence.
  - intros. simpl inv. rewrite proposition_2.
    simpl in *. rewrite IHf1. rewrite IHf2. apply firstn_skipn.
    rewrite arity_inv. reflexivity.
  - nil_case l. simpl. rewrite iter_inverse; auto.
  - nil_case l. simpl inv. rewrite co_if. simpl in *.
    destruct z; congruence.
Qed.

Theorem proposition_1_r_co : ∀ f l, «inv f;;f» l = l.
Proof.
  intros. rewrite <- (inv_involute f) at 2. apply proposition_1_l_co.
Qed.

Theorem proposition_1_l : ∀ f l, «inv f» («f» l) = l.
Proof. intros. rewrite <- (proposition_1_l_co f). reflexivity. Qed.

Theorem proposition_1_r : ∀ f l, «f» («inv f» l) = l.
Proof. intros. rewrite <- (proposition_1_r_co f). reflexivity. Qed. 

Theorem proposition_1 : ∀ f l m, «f» l = m <-> «inv f» m = l.
Proof.
  split.
  - intros. subst. apply proposition_1_l.
  - intros. subst. apply proposition_1_r.
Qed.

(* Principio di induzione per i numeri interi. Sarebbe stato più utile con la definizione originale di It, invece con la definizione che ho dato io non serve a molto. *)

Open Scope Z.
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

Lemma list_eq : ∀ X (x y : X) l m, x::l = y::m → x=y ∧ l=m.
Proof. split; congruence. Qed.

Lemma inc_pos : ∀ p y, «inc» [Zpos p;y] = [Zpos p;y + Zpos p].
Proof.
  intros. induction p using Pos.peano_ind.
  - reflexivity.
  - unfold inc in *. rewrite ev_it in *. f_equal.
    lets (_ & IHt) : list_eq IHp.
    replace (Z.pos (Pos.succ p)) with (Z.pos p + 1); try lia.
    replace (Z.to_nat(Z.pos p+1)) with (S(Z.to_nat (Z.pos p))); try lia.
    rewrite iter_succ. rewrite IHt. simpl. f_equal. lia.
Qed.

Lemma inc_def : ∀ x y, 0 <= x → «inc» [x;y] = [x;y+x].
Proof.
  intros. destruct x.
  - simpl. f_equal. f_equal. lia.
  - apply inc_pos.
  - contradiction.
Qed.

Lemma dec_def : ∀ x y, 0 <= x → «dec» [x;y] = [x;y-x].
Proof.
  intros. rewrite proposition_1.
  replace (inv dec) with inc. rewrite inc_def. repeat f_equal. lia.
  auto. auto.
Qed.

Ltac simpl_splice := unfold splice; simpl firstn; simpl skipn;
  try rewrite !firstn_eq_splice.

Lemma firstn_ev : ∀ f n l, arity f ≤ n →
  («f» l)^[0,n] = «f» (l^[0,n]).
Proof.
  intros. gen n l. induction f; intros;
  try (destruct n; destruct l; liast; fail).
  - destruct n; destruct l; liast.
    destruct n; destruct l; liast.
  - simpl in *.
    rewrite IHf2. rewrite IHf1.
    all: liast.
  - simpl in *. rewrite splice_app.
    rewrite splice_all. rewrite splice_comp.
    repeat f_equal. lia.
    rewrite IHf2. f_equal.
    rewrite skipn_comp_splice. rewrite splice_comp_skipn.
    all: liast.
    destruct (Nat.le_ge_cases (arity f1) (length l)).
    + f_equal. all:liast.
    + rewrite !splice_all2. all: liast.
  - destruct n. liast.
    destruct l. liast. simpl_splice. simpl. f_equal.
    induction (Z.to_nat z). reflexivity.
    simpl. rewrite IHf. rewrite IHn0. all: liast.
  - destruct n. liast.
    destruct l. liast.
    simpl in H. destruct z;
    simpl_splice; simpl; f_equal;
    intuition.
Qed.

Lemma skipn_ev : ∀ f n l, arity f ≤ n →
  («f» l)^[n,∞] = l^[n,∞].
Proof.
  intros. gen n l. induction f; intros;
  try (destruct n; destruct l; liast; fail).
  - destruct n; destruct l; liast.
    destruct n; destruct l; liast.
  - simpl in *.
    rewrite IHf2. rewrite IHf1.
    all: liast.
  - simpl in *. rewrite skipn_app.
    rewrite skipn_all2. rewrite IHf2.
    rewrite skipn_skipn. all: liast.
    destruct (Nat.le_ge_cases (arity f1) (length l)).
    + f_equal. liast.
    + rewrite !skipn_all2. all: liast.
  - destruct n. liast.
    destruct l. liast. simpl in *.
    induction (Z.to_nat z). reflexivity.
    simpl. rewrite IHf. rewrite IHn0. all: liast.
  - destruct n. liast.
    destruct l. liast.
    destruct z; simpl in *; intuition.
Qed.

Lemma longer : ∀ f l,
  «f» l = «f» (l^[0,arity f]) ++ l^[arity f,∞].
Proof.
  intros. rewrite <- firstn_ev. rewrite <- skipn_ev with (f:=f).
  rewrite splice_app_skipn. all: liast.
Qed.

Notation Zp := Zpos.
Notation Zn := Zneg.

(* Nota: le seguenti sono tattiche utili nelle dimostrazioni riguardanti le definizioni delle funzioni. *)

Ltac partial := rewrite longer; simpl_splice.
Ltac segment := repeat rewrite co_def.
Ltac equal_list := unfold app; auto; repeat f_equal; lia.

Open Scope nat.
Definition cp' (n m : nat) := (list_sum (seq 1 (n+m)) + n).

Lemma list_sum_last : ∀ n : nat,
  list_sum (seq 1 (S n)) = list_sum (seq 1 n) + (S n).
Proof.
  intros. rewrite seq_S. rewrite list_sum_app.
  simpl. lia.
Qed.

Open Scope Z.

Lemma up_add : ∀ n m, ↑n + ↑m = ↑(n + m).
Proof. lia. Qed.
Lemma up_sub : ∀ n m, m ≤ n → ↑n - ↑m = ↑(n - m).
Proof. lia. Qed.

Lemma tr_def : ∀ n : nat,
  «tr» [↑n; 0; 0] = [↑n; ↑n; ↑list_sum (seq 1 n)].
Proof.
  intros. unfold tr. rewrite ev_it. f_equal. induction n.
  - reflexivity.
  - rewrite list_sum_last.
    rewrite Nat2Z.id in *.
    rewrite iter_succ. rewrite IHn.
    segment. partial. rewrite inc_def.
    simpl app. f_equal. lia.
    replace (↑n + 1) with (↑(S n)). rewrite up_add. all: liast.
Qed.

Lemma cp_def : ∀ n m : nat,
  «cp» [↑n; ↑m; 0; 0] = [↑n; ↑m; ↑(cp' n m); 0].
Proof.
  intros. unfold cp. segment.
  asserts_rewrite (
    « inc » [↑ n; ↑ m; 0; 0] = [↑ n; ↑ m + ↑ n; 0; 0]).
  { partial. rewrite inc_def. equal_list. lia. }
  asserts_rewrite (↑m + ↑n = ↑n + ↑m). lia.
  asserts_rewrite (
  «id ‖ (tr;; dec)» [↑n;↑n + ↑m;0;0] =
    ↑n :: («tr;; dec» [↑n + ↑m;0;0]) ).
  { reflexivity. }
  segment.
  asserts_rewrite (
    «tr» [↑n+↑m; 0; 0] =
    [↑n+↑m; ↑n+↑m; ↑list_sum (seq 1 (n+m))] ).
  { rewrite up_add. apply tr_def. }
  asserts_rewrite (
    «dec» [↑n+↑m; ↑n+↑m; ↑list_sum (seq 1 (n+m))] =
    [↑n+↑m; 0; ↑list_sum (seq 1 (n+m))] ).
  { partial. rewrite dec_def.
    replace (↑n+↑m - (↑n+↑m)) with 0. auto. all: lia. }
  asserts_rewrite (
    «dec» [↑n; ↑n+↑m; 0; ↑list_sum (seq 1 (n + m))] =
    [↑n; ↑m; 0; ↑list_sum (seq 1 (n + m))] ).
  { partial.
    rewrite dec_def. replace (↑n+↑m-↑n) with (↑m).
    auto. all: lia. }
  asserts_rewrite (
    «\[0;3;1]%nat\» [↑n; ↑m; 0; ↑list_sum (seq 1 (n+m))] =
    [↑n; ↑list_sum (seq 1 (n+m)); ↑m; 0] ).
  { reflexivity. }
  asserts_rewrite (
    «inc» [↑n; ↑list_sum (seq 1 (n+m)); ↑m; 0] =
    [↑n; ↑list_sum (seq 1 (n+m)) + ↑n; ↑m; 0] ).
  { partial.
    rewrite inc_def. auto. lia. }
  unfold cp'. simpl. repeat f_equal. lia.
Qed.

Definition cu'_fst (n m : nat) :=
  match m with
  | O => O
  | _ => S n
  end.

Definition cu'_snd (n m : nat) :=
  match m with
  | O => S n
  | _ => pred m
  end.

Lemma gt0_positive : ∀ n : Z, 0 < n → ∃ p : positive, n = Zp p.
Proof.
  intros. destruct n; try discriminate. eauto.
Qed.

Lemma clean_up : ∀ n,
  match Pos.of_succ_nat n with
  | (p~1)%positive => Zp p~0
  | (p~0)%positive => Zp (Pos.pred_double p)
  | 1%positive => 0
  end = ↑ n.
Proof.
  intros. replace (↑ n) with (↑ S n - 1). 2:lia.
  reflexivity.
Qed.

Lemma cu_step_def : ∀ n m,
  «cu_step» [↑n; ↑m; 0] = [↑cu'_fst n m; ↑cu'_snd n m; 0].
Proof.
  intros.
  destruct n; destruct m.
  - reflexivity.
  - simpl. rewrite clean_up. reflexivity.
  - simpl. f_equal. f_equal. lia.
  - simpl. rewrite clean_up. f_equal. lia.
Qed.

Lemma cu_step_z : ∀ m,
  «cu_step» [↑m; 0; 0] = [0; ↑m + 1; 0].
Proof.
  intros. replace 0 with (↑O). 2:lia. rewrite cu_step_def.
  simpl. equal_list.
Qed.

Lemma cu_step_p : ∀ n m, (O < m)%nat →
  «cu_step» [↑n; ↑m; 0] = [↑n + 1; ↑m - 1; 0].
Proof.
  intros. rewrite cu_step_def.
  unfold cu'_fst. unfold cu'_snd. destruct m.
  - lia.
  - simpl. rewrite clean_up. f_equal. lia.
Qed.

Lemma cu_step_le : ∀ n m k, k ≤ m →
  iter «cu_step» k [↑n; ↑m; 0] = [↑n + ↑k; ↑m - ↑k; 0].
Proof.
  intros. induction k as [k IH] using lt_wf_ind.
  destruct k.
  - intros. simpl. equal_list.
  - rewrite iter_succ. rewrite IH.
    rewrite !up_add. rewrite !up_sub. rewrite cu_step_p.
    equal_list.
  all:lia.
Qed.

Open Scope nat.
Lemma cp'_Sn : ∀ n m, cp' (S n) m = cp' n m + n + m + 2.
Proof.
  intros. unfold cp'. replace (S n + m) with (S (n + m)).
  rewrite list_sum_last. lia. lia.
Qed.
Lemma cp'_Sm : ∀ n m, cp' n (S m) = cp' n m + n + m + 1.
Proof.
  intros. unfold cp'. replace (n + S m) with (S (n + m)).
  rewrite list_sum_last. lia. lia.
Qed.

Lemma iter_add : ∀ X (f : X → X) n m x,
  iter f (n + m) x = iter f n (iter f m x).
Proof. intros. induction n.
  - reflexivity.
  - change (S n + m) with (S (n + m)). rewrite iter_succ.
    rewrite IHn. reflexivity.
Qed.

Lemma iter_one : ∀ X (f : X → X) x,
  iter f 1 x = f x.
Proof. reflexivity. Qed.

Open Scope Z.
Lemma cu_step_Sn : ∀ n m,
  iter «cu_step» (cp' n m) [0; 0; 0] = [↑n; ↑m; 0] →
  iter «cu_step» (cp' (S n) m) [0; 0; 0] = [↑n + 1; ↑m; 0].
Proof.
  intros. rewrite cp'_Sn.
  replace (cp' n m +n+m+2)%nat with
    ((((1+n)+1)+m)+(cp' n m))%nat.
  repeat rewrite iter_add. rewrite H.
  rewrite cu_step_le.
  replace (↑m - ↑m) with 0. rewrite !iter_one.
  rewrite up_add. rewrite cu_step_z.
  replace (↑(n + m) + 1) with (↑(n + m + 1)).
  replace 0 with (↑O). rewrite cu_step_le.
  rewrite up_sub. replace (↑0 + ↑n) with (↑n).
  rewrite cu_step_p. equal_list. all:lia.
Qed.

Lemma cu_step_Sm : ∀ n m,
  iter «cu_step» (cp' n m) [0; 0; 0] = [↑n; ↑m; 0] →
  iter «cu_step» (cp' n (S m)) [0; 0; 0] = [↑n; ↑m + 1; 0].
Proof.
  intros. rewrite cp'_Sm.
  replace (cp' n m +n+m+1)%nat with
    (((n+1)+m)+(cp' n m))%nat.
  repeat rewrite iter_add. rewrite H.
  rewrite cu_step_le.
  replace (↑m - ↑m) with 0. rewrite !iter_one.
  rewrite up_add. rewrite cu_step_z.
  replace (↑(n + m) + 1) with (↑(n + m + 1)).
  replace 0 with (↑O). rewrite cu_step_le.
  rewrite up_sub. replace (↑0 + ↑n) with (↑n).
  equal_list. all:lia.
Qed.

Lemma cu_def_iter : ∀ n m,
  iter «cu_step» (cp' n m) [0; 0; 0] = [↑n; ↑m; 0].
Proof.
  intros. induction n; induction m.
  - reflexivity.
  - rewrite cu_step_Sm. equal_list. auto.
  - rewrite cu_step_Sn. equal_list. auto.
  - rewrite cu_step_Sn. equal_list. auto.
Qed.

Lemma cu_def : ∀ n m,
  «cu» [↑cp' n m; 0; 0; 0] = [↑cp' n m; ↑n; ↑m; 0].
Proof.
  intros.
  unfold cu. rewrite ev_it. rewrite Nat2Z.id.
  rewrite cu_def_iter. reflexivity.
Qed.

Lemma push_def : ∀ n m,
  «push» [↑n; ↑m; 0; 0] = [↑cp' n m; 0; 0; 0].
Proof.
  intros. unfold push. segment.
  rewrite cp_def.
  simpl («\[2;0;1]%nat\» [↑n; ↑m; ↑cp' n m; 0]).
  rewrite <- proposition_1. rewrite cu_def. reflexivity.
Qed.

Lemma up_def : ∀ x l, ↑↑(x::l) = ↑x::↑↑l.
Proof. reflexivity. Qed.

Open Scope Z.
Lemma id_swap_def : ∀ n l, (2+n ≤ length l)%nat →
  «Id n ‖ Sw» l =
  l^[0,n] ++ l^[1+n] ++ l^[n] ++ l^[2+n,∞].
Proof.
  intros.
  rewrite pa_def. simpl arity. rewrite id_def. f_equal.
  replace (l^[1+n]) with ((l^[n,∞])^[1]).
  replace (l^[n]) with ((l^[n,∞])^[0]).
  replace (l^[2+n,∞]) with ((l^[n,∞])^[2,∞]).
  remember (l^[n,∞]) as m.
  destruct m. liast.
  destruct m. liast. reflexivity.
  rewrite skipn_skipn. reflexivity.
  rewrite skipn_comp_splice. f_equal. all: liast.
  rewrite skipn_comp_splice. f_equal. all: liast.
Qed.

Open Scope nat.

Create HintDb arith_base.
Hint Rewrite
  Nat.sub_0_r
  Nat.add_0_l
  Nat.sub_diag 
  Nat.add_sub
  Nat.add_0_r : arith_base.

Lemma call_def : ∀ n l, n < length l →
  «call n» l = l^[n] ++ l^[0,n] ++ l^[1+n, ∞].
Proof.
  intros. gen l. induction n.
  - intros. destruct l. all: liast.
  - intros. change (S n) with (1+n).
    simpl call. segment. rewrite IHn.
    replace (l^[0,1+n]) with (l^[0,n] ++ l^[n]).
    replace ((« Id n ‖ Sw » l)^[1+n,∞])
    with ((« Id n ‖ Sw » l)^[1+n] ++ (« Id n ‖ Sw » l)^[2+n,∞]).
    rewrite <- app_assoc. rewrite id_swap_def.

    rewrite !splice_app. rewrite !skipn_app.
    rewrite !splice_comp. rewrite !splice_comp_skipn.
    rewrite !skipn_comp_splice. rewrite !skipn_skipn.
    rewrite <- !app_assoc. rewrite !splice_length.
    repeat (try (rewrite min_l; [| lia]);
            try (rewrite min_r; [| lia])).

    autorewrite with arith_base.

    rewrite !splice_same. rewrite !app_nil_l.
    f_equal.
    f_equal.
    rewrite splice_gt. rewrite app_nil_l.
    rewrite splice_gt. rewrite app_nil_l.
    f_equal. f_equal. lia.
    rewrite splice_gt. rewrite app_nil_l.
    rewrite splice_gt. rewrite app_nil_l.
    rewrite splice_gt. rewrite app_nil_l.
    rewrite splice_gt. rewrite app_nil_l.
    f_equal. all: try lia.

    apply splice_app_skipn; lia.
    apply app_splice; lia.
    rewrite length_evaluate; lia.
Qed.

Open Scope Z.

Lemma perm_n_0 : ∀ n l, (n < length l)%nat → «\[n;0]%nat\» l =
  l^[n] ++ l^[0,n] ++ l^[1+n,∞].
Proof.
  intros. unfold perm. simpl prepare. simpl rev.
  replace (n+0)%nat with n. remember (S n) as m. simpl call_list.
  segment. rewrite id_def. rewrite call_def. subst. all: liast.
Qed.

Lemma inv_perm_n_0 : ∀ n l, (n < length l)%nat →
  «inv (\[n;0]%nat\)» l = l^[1,1+n] ++ l^[0] ++ l^[1+n,∞].
Proof.
  intros. rewrite <- proposition_1. rewrite perm_n_0.
  rewrite !splice_app. rewrite !skipn_app.
  rewrite !splice_comp. rewrite !splice_comp_skipn.
  rewrite !skipn_comp_splice. rewrite !skipn_skipn.
  rewrite <- !app_assoc. rewrite !splice_length.
  repeat (try (rewrite min_l; [| lia]);
          try (rewrite min_r; [| lia])).
  autorewrite with arith_base.
  repeat (try (rewrite splice_app_skipn'; [| lia | lia]);
          try (rewrite splice_gt''; [| lia])).
  replace (n-(1+n-1))%nat with O. reflexivity.
  all: try lia. liast.
Qed.

Lemma cons_app : ∀ X (x : X) l, x::l = [x]++l.
Proof. reflexivity. Qed.

Lemma conv_su_def : ∀ i n l x, length l = n → (i < n)%nat →
  «conv_su i n» (x::↑↑l) = x + ↑ S (nth i l O) :: ↑↑l.
Proof.
  intros. unfold conv_su. segment.
  rewrite id_def. rewrite su_def.
  asserts_rewrite (
    «\[S i; 0%nat]\» (x+1 :: ↑↑l) =
    (↑↑l)^[i] ++ x+1 :: (↑↑l)^[0,i] ++ (↑↑l)^[1+i,∞]).
  { rewrite perm_n_0. simpl_splice. reflexivity.
    simpl. rewrite map_length. lia. }
  rewrite !map_splice. rewrite map_skipn.
  rewrite (splice_nth l O).
  asserts_rewrite (
    ↑↑ [nth i l 0%nat] ++ x+1 :: ↑↑ l ^[0,i] ++ ↑↑l^[1+i,∞] =
    ↑(nth i l O) :: x + 1 :: ↑↑l^[0,i] ++ ↑↑l^[1+i,∞]).
  { reflexivity. }
  asserts_rewrite (
    «inc» (↑nth i l 0%nat :: x+1 :: ↑↑l^[0,i] ++ ↑↑l^[1+i,∞]) =
    ↑nth i l 0%nat :: x+1+↑nth i l 0%nat :: ↑↑l^[0,i] ++ ↑↑l^[1+i,∞]).
  { partial. rewrite inc_def. reflexivity. lia. }
  asserts_rewrite (
    ↑nth i l O :: x+1+↑nth i l O :: ↑↑l ^[0,i] ++ ↑↑l^[1+i,∞] =
    [↑nth i l O]++[x+1+↑nth i l O]++↑↑l ^[0,i] ++ ↑↑l^[1+i,∞]).
  { reflexivity. }
  rewrite inv_perm_n_0. rewrite <- map_splice. rewrite <- map_skipn.

  (* sarebbe carino avere tattiche per questi tipi di goal *)

    rewrite !splice_app. rewrite !skipn_app.
    rewrite <- !app_assoc. simpl length.
    rewrite !skipn_skipn.
    rewrite splice_length.
  repeat (try (rewrite min_l; [| rewrite map_length; lia]);
          try (rewrite min_r; [| rewrite map_length; lia])).
  autorewrite with arith_base.
  rewrite splice_all2. rewrite app_nil_l.
  symmetry. rewrite cons_app. f_equal.
  rewrite splice_all. f_equal. lia. simpl. lia.
  replace (↑ nth i l 0%nat) with (nth i (↑↑l) 0).
  rewrite <- splice_nth.
  rewrite !splice_comp. rewrite !splice_comp_skipn.
  rewrite !skipn_comp_splice.
  repeat (try (rewrite min_l; [| lia]);
          try (rewrite min_r; [| lia])).
  autorewrite with arith_base.
  replace ([x + 1 + nth i (↑↑ l) 0] ^[ 0 - 1, 0]) with ([]:list Z).
  replace ([x + 1 + nth i (↑↑ l) 0] ^[ 1 + S i - 1, ∞ ]) with ([]:list Z).
  rewrite !app_nil_l.
  repeat (try (rewrite splice_app_skipn'; [| lia | lia]);
          try (rewrite splice_gt''; [| lia])).
  reflexivity.
  liast. rewrite skipn_nil. reflexivity.
  liast. rewrite map_length. lia.
  replace 0 with (↑O). rewrite map_nth. reflexivity. lia.
  liast.
  rewrite cons_app.
  replace (↑nth i l 0%nat :: ↑↑ l ^[ 0, i])
  with([↑nth i l 0%nat] ++ ↑↑ l ^[ 0, i]).
  liast. autorewrite with arith_base. rewrite map_length. liast.
  reflexivity.
  lia.
Qed.

Lemma conv_pr_def : ∀ i n l x, length l = n → (i < n)%nat →
  «conv_pr i n» (x::↑↑l) = x + ↑ (nth i l O) :: ↑↑l.
Proof.
  intros. unfold conv_pr. segment.
  rewrite id_def.
  asserts_rewrite (
    «\[S i; 0%nat]\» (x :: ↑↑l) =
    (↑↑l)^[i] ++ x :: (↑↑l)^[0,i] ++ (↑↑l)^[1+i,∞]).
  { rewrite perm_n_0. simpl_splice. reflexivity.
    simpl. rewrite map_length. lia. }
  rewrite !map_splice. rewrite map_skipn.
  rewrite (splice_nth l O).
  asserts_rewrite (
    ↑↑ [nth i l 0%nat] ++ x :: ↑↑ l ^[0,i] ++ ↑↑l^[1+i,∞] =
    ↑(nth i l O) :: x :: ↑↑l^[0,i] ++ ↑↑l^[1+i,∞]).
  { reflexivity. }
  asserts_rewrite (
    «inc» (↑nth i l 0%nat :: x :: ↑↑l^[0,i] ++ ↑↑l^[1+i,∞]) =
    ↑nth i l 0%nat :: x+↑nth i l 0%nat :: ↑↑l^[0,i] ++ ↑↑l^[1+i,∞]).
  { partial. rewrite inc_def. reflexivity. lia. }
  asserts_rewrite (
    ↑nth i l O :: x+↑nth i l O :: ↑↑l ^[0,i] ++ ↑↑l^[1+i,∞] =
    [↑nth i l O]++[x+↑nth i l O]++↑↑l ^[0,i] ++ ↑↑l^[1+i,∞]).
  { reflexivity. }
  rewrite inv_perm_n_0. rewrite <- map_splice. rewrite <- map_skipn.

    rewrite !splice_app. rewrite !skipn_app.
    rewrite <- !app_assoc. simpl length.
    rewrite !skipn_skipn.
    rewrite splice_length.
  repeat (try (rewrite min_l; [| rewrite map_length; lia]);
          try (rewrite min_r; [| rewrite map_length; lia])).
  autorewrite with arith_base.
  rewrite splice_all2. rewrite app_nil_l.
  symmetry. rewrite cons_app. f_equal.
  rewrite splice_all. f_equal. simpl. lia.
  replace (↑ nth i l 0%nat) with (nth i (↑↑l) 0).
  rewrite <- splice_nth.
  rewrite !splice_comp. rewrite !splice_comp_skipn.
  rewrite !skipn_comp_splice.
  repeat (try (rewrite min_l; [| lia]);
          try (rewrite min_r; [| lia])).
  autorewrite with arith_base.
  replace ([x + nth i (↑↑ l) 0] ^[ 0 - 1, 0]) with ([]:list Z).
  replace ([x + nth i (↑↑ l) 0] ^[ 1 + S i - 1, ∞ ]) with ([]:list Z).
  rewrite !app_nil_l.
  repeat (try (rewrite splice_app_skipn'; [| lia | lia]);
          try (rewrite splice_gt''; [| lia])).
  reflexivity.
  liast. rewrite skipn_nil. reflexivity.
  liast. rewrite map_length. lia.
  replace 0 with (↑O). rewrite map_nth. reflexivity. lia.
  liast.
  rewrite cons_app.
  replace (↑nth i l 0%nat :: ↑↑ l ^[ 0, i])
  with([↑nth i l 0%nat] ++ ↑↑ l ^[ 0, i]).
  liast. autorewrite with arith_base. rewrite map_length. liast.
  reflexivity.
  lia.
Qed.


Lemma thesis_ze : ∀ n l x, thesis (ZE n) l x.
Proof.
  unfold thesis. simpl. intros. equal_list.
Qed.

Open Scope nat.
Lemma arity_call : ∀ n, arity (call n) = 1+n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. lia.
Qed.

Lemma arity_conv_su : ∀ i n, i < n → arity (conv_su i n) = 1+n.
Proof.
  intros. unfold conv_su. simpl arity.
  rewrite arity_inv. rewrite arity_call.
  autorewrite with arith_base.
  replace (max (i+2) (1+i)) with (i+2).
  replace (max (1+i) (i+2)) with (i+2).
  replace (i+2) with (2+i). simpl. all: lia.
Qed.

Lemma thesis_su : ∀ i n l x, thesis (SU i n) l x.
Proof.
  unfold thesis. intros. unfold convert.
  replace (anc (SU i n)) with O.
  simpl repeat. rewrite app_nil_r.
  rewrite conv_su_def. reflexivity.
  simpl in H0. easy.
  inverts H. easy.
  unfold anc. unfold convert.
  assert (arity (conv_su i n) ≤ 1+ARITY (SU i n)).
  { simpl ARITY. rewrite arity_conv_su. easy.
    inverts H. easy. }
  lia.
Qed.

Lemma arity_conv_pr : ∀ i n, i < n → arity (conv_pr i n) = 1+n.
Proof.
  intros. unfold conv_pr. simpl arity.
  rewrite arity_inv. rewrite arity_call.
  autorewrite with arith_base.
  replace (max (i+2) (1+i)) with (i+2).
  replace (max (1+i) (i+2)) with (i+2).
  replace (i+2) with (2+i). simpl. all: lia.
Qed.

Lemma thesis_pr : ∀ i n l x, thesis (PR i n) l x.
Proof.
  unfold thesis. intros. unfold convert.
  replace (anc (PR i n)) with O.
  simpl repeat. rewrite app_nil_r.
  rewrite conv_pr_def. reflexivity.
  simpl in H0. easy.
  inverts H. easy.
  unfold anc. unfold convert.
  assert (arity (conv_pr i n) ≤ 1+ARITY (PR i n)).
  { simpl ARITY. rewrite arity_conv_pr. easy.
    inverts H. easy. }
  lia.
Qed.

(* Nota: depth serve unicamente per fare induzione correttamente su CO F Gs. *)

Fixpoint depth (F : PRF) : nat :=
  match F with
  | ZE n => O
  | SU i n => O
  | PR i n => O
  | CO F Gs => max (1+depth F) (1+list_max (map depth Gs))
  | RE F G => max (depth F) (depth G)
  end.

Lemma convert_re_def : ∀ F G, convert (RE F G) =
  id ‖ re_forward (ARITY F) (convert F) (convert G) ;;
  \[6;0]\ ;; inc ;; inv (\[6;0]\) ;;
  id ‖ inv (re_forward (ARITY F) (convert F) (convert G)).
Proof. reflexivity. Qed.

Lemma convert_co_def : ∀ F Gs, convert (CO F Gs) =
  let (n, m) := (ARITY (CO F Gs), length Gs) in
  id ‖ co_loading n (map convert Gs) ;; \seq (1+m) n\ ;;
  Id n ‖ (convert F) ;;
  inv (id ‖ co_loading n (map convert Gs) ;; \seq (1+m) n\).
Proof. reflexivity. Qed.

Lemma arity_co_def : ∀ f g, arity (f ;; g) = max (arity f) (arity g).
Proof. reflexivity. Qed.

Lemma arity_pa_def : ∀ f g, arity (f ‖ g) = arity f + arity g.
Proof. reflexivity. Qed.

Lemma arity_convert_re : ∀ F G,
  S (ARITY (RE F G)) ≤ arity (convert (RE F G)).
Proof.
  intros. simpl ARITY. rewrite convert_re_def.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_pa_def. simpl (arity id).
  apply le_n_S. unfold re_forward.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_pa_def. simpl arity. lia.
Qed.

Lemma ARITY_le_arity_le :
  ∀ F d, depth F ≤ d → strict F → S (ARITY F) ≤ arity (convert F).
Proof.
  intros. gen F. induction d.
  - intros. induction F.
    + simpl. easy.
    + unfold convert. rewrite arity_conv_su.
      simpl. easy. inverts H0. easy.
    + unfold convert. rewrite arity_conv_pr.
      simpl. easy. inverts H0. easy.
    + simpl in H. lia.
    + apply arity_convert_re. 
  - intros. induction F.
    + simpl. easy.
    + unfold convert. rewrite arity_conv_su.
      simpl. easy. inverts H0. easy.
    + unfold convert. rewrite arity_conv_pr.
      simpl. easy. inverts H0. easy.
    + destruct Gs.
      * simpl. lia.
      * inverts H0.
        asserts_rewrite (ARITY (CO F (p :: Gs)) = ARITY p).
        { apply Forall_inv in H6. easy. }
        rewrite convert_co_def.
        rewrite arity_co_def. rewrite Nat.max_le_iff. left.
        rewrite arity_co_def. rewrite Nat.max_le_iff. left.
        rewrite arity_co_def. rewrite Nat.max_le_iff. left.
        rewrite arity_pa_def. simpl (arity id). apply le_n_S.
        simpl co_loading. rewrite max_l.
        rewrite arity_co_def. rewrite Nat.max_le_iff. left.
        rewrite arity_co_def. rewrite Nat.max_le_iff. left.
        unfold perm. simpl. rewrite arity_call. lia.
        apply Forall_inv in H6. simpl in H6. lia.
    + apply arity_convert_re.
Qed.

Lemma ARITY_le_arity :
  ∀ F, strict F → S (ARITY F) ≤ arity (convert F).
Proof.
  intros. rewrite ARITY_le_arity_le with (d:=depth F).
  all: easy.
Qed.

Open Scope Z.
Lemma thesis_le : ∀ F l x n, thesis F l x → anc F ≤ n →
  strict F →
  ARITY F = length l →
  «convert F» (x :: ↑↑l ++ repeat 0 n) =
  x + ↑(EVALUATE F l) :: ↑↑l ++ repeat 0 n.
Proof.
  intros. unfold thesis in H.
  rewrite longer.
  asserts_rewrite (
    (x :: ↑↑ l ++ repeat 0 n) ^[ 0, arity (convert F)] =
    (x :: ↑↑ l ++ repeat 0 (anc F)) ).
  { rewrite !app_comm_cons. rewrite splice_app.
    rewrite splice_all. f_equal. rewrite repeat_splice.
    unfold anc in *. f_equal. simpl.
    rewrite map_length. lia. simpl. rewrite map_length.
    rewrite <- H2. rewrite ARITY_le_arity; easy. }
  rewrite H.
  rewrite !app_comm_cons. rewrite <- app_assoc. f_equal.
  unfold anc. rewrite skipn_app.
  rewrite skipn_all2. rewrite app_nil_l.
  rewrite repeat_skipn. rewrite <- repeat_app.
  f_equal. simpl. rewrite map_length.
  unfold anc in H0. lia.
  simpl. rewrite map_length.
  rewrite <- H2. apply ARITY_le_arity; easy.
  all: easy.
Qed.

Lemma length_filter_le : ∀ X (f : X → bool) l,
  length (filter f l) ≤ length l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. destruct (f a); simpl; lia.
Qed.

Lemma length_filter_all : ∀ X (f : X → bool) l,
  length (filter f l) = length l ↔ Forall (λ x, f x = true) l.
Proof.
  intros. split; intros.
  - rewrite Forall_forall. intros. induction l.
    + false.
    + assert (f a = true).
      { destruct (Sumbool.sumbool_of_bool (f a)). easy.
        simpl in H. rewrite e in H.
        assert (H1:=length_filter_le f l). lia. }
      destruct H0.
      * now subst.
      * simpl in H. rewrite H1 in H. simpl in H. injection H as H2.
        now apply IHl.
  - induction l.
    + reflexivity.
    + simpl. assert(H1:=H).
      apply Forall_inv in H. rewrite H.
      apply Forall_inv_tail in H1.
      simpl. f_equal. apply IHl. easy.
Qed.

Lemma call_list_app : ∀ l l0 l1,
  «call_list (l0 ++ l1)» l = «call_list l0 ;; call_list l1» l.
Proof.
  intros. gen l. induction l0.
  - reflexivity.
  - intros. simpl in *. apply IHl0.
Qed.

Open Scope nat.
Lemma perm_seq : ∀ l m a, a ≤ length m →
  «\seq (length l) a\» (l++m) = m^[0,a] ++ l ++ m^[a,∞].
Proof.
  intros. gen l m. induction a; intros.
  - reflexivity.
  - unfold perm. simpl seq.
    asserts_rewrite (
      prepare (length l :: seq (S (length l)) a) =
      length l + a :: prepare (seq (S (length l)) a) ).
    { simpl. f_equal. f_equal.
      replace (length (filter (λ j : nat, length l <? j) (seq (S (length l)) a)) =
        a)
      with (length (filter (λ j : nat, length l <? j) (seq (S (length l)) a)) =
        length (seq (S (length l)) a)).
      rewrite length_filter_all.
      rewrite Forall_forall. intros.
      rewrite Nat.ltb_lt. apply in_seq in H0. lia.
      f_equal. rewrite seq_length. reflexivity. }
    simpl rev.
    asserts_rewrite (
      «call_list (rev (prepare (seq (S (length l)) a)) ++
        [length l + a])» (l ++ m) =
      «call_list (rev (prepare (seq (S (length l)) a))) ;;
        call (length l + a)» (l ++ m) ).
    { remember (length l) as n. generalize (l ++ m).
      induction (rev (prepare (seq (S n) a))); intros.
      - simpl. reflexivity.
      - simpl in *. apply IHl0. }
    segment. replace (l++m) with ((l ++ m^[0]) ++ m^[1,∞]).
    replace (S (length l)) with (length (l ++ m^[0])).
    unfold perm in IHa. rewrite IHa.
    destruct m. simpl in H. lia. simpl_splice.
    rewrite <- app_assoc. rewrite <- !app_comm_cons. simpl.
    rewrite app_assoc. simpl in H. apply le_S_n in H.
    rewrite call_def.
    rewrite splice_app_l. autorewrite with arith_base.
    change ((z :: m ^[ a, ∞ ]) ^[ 0, 1]) with [z].
    rewrite firstn_app_l.
    replace ((m ^[ 0, a] ++ l) ++ z :: m ^[ a, ∞ ])
      with ((m^[0,a] ++ l ++ [z]) ++ m^[a,∞]).
    rewrite skipn_app_l. simpl. rewrite app_assoc. reflexivity.
    rewrite !app_length. rewrite splice_length. simpl. lia.
    rewrite <- !app_assoc. reflexivity.
    rewrite app_length. rewrite splice_length. lia.
    rewrite app_length. rewrite splice_length. lia.
    rewrite !app_length. rewrite splice_length. simpl.
    rewrite skipn_length. lia.
    rewrite skipn_length. lia.
    rewrite app_length. rewrite splice_length. lia.
    rewrite <- app_assoc. f_equal.
    rewrite <- firstn_eq_splice. simpl (1+0).
    apply firstn_skipn.
Qed.

Lemma eq_tail : ∀ X (x : X) l l', x::l = x::l' → l=l'.
Proof.
  intros. injection H. easy.
Qed.

Lemma anc_re_l : ∀ F G, strict (RE F G) → 6 + anc G ≤ anc (RE F G).
Proof.
  intros. unfold anc. inverts H. simpl ARITY.
  asserts_rewrite (
    6 + (arity (convert G) - (1 + ARITY G)) =
    5 + arity (convert G) - ARITY G ).
  { assert (H := ARITY_le_arity H3). lia. }
  asserts_rewrite (
    arity (convert (RE F G)) - (1 + S (ARITY F)) =
    arity (convert (RE F G)) - ARITY G ).
  { lia. }
  apply Nat.sub_le_mono_r.
  rewrite convert_re_def.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_pa_def. simpl (arity id).
  change 5 with (1+4). apply plus_le_compat_l with (p:=1).
  change (S (S (S (S (arity (convert G)))))) with (4+arity (convert G)).
  unfold re_forward.
  rewrite arity_co_def. rewrite Nat.max_le_iff. right.
  simpl arity. lia.
Qed.

Lemma anc_re_r : ∀ F G, strict (RE F G) → 6 + anc F ≤ anc (RE F G).
Proof.
  intros. unfold anc. inverts H. simpl ARITY.
  asserts_rewrite (
    6 + (arity (convert F) - (1 + ARITY F)) =
    7 + arity (convert F) - (2 + ARITY F) ).
  { assert (H := ARITY_le_arity H2). lia. }
  asserts_rewrite (
    arity (convert (RE F G)) - (1 + S (ARITY F)) =
    arity (convert (RE F G)) - (2 + ARITY F) ).
  { lia. }
  apply Nat.sub_le_mono_r.
  rewrite convert_re_def.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_pa_def. simpl (arity id).
  change 7 with (1+6). apply plus_le_compat_l with (p:=1).
  change (S(S(S(S(S(S(arity (convert F)))))))) with (6+arity (convert F)).
  unfold re_forward.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. right.
  reflexivity.
Qed.

Lemma anc_re_6 : ∀ F G, strict (RE F G) → 6 ≤ anc (RE F G).
Proof.
  intros. assert (H0:=anc_re_l H). lia.
Qed.

Open Scope Z.
Lemma re_forward_def : ∀ F G y ys,
  strict (RE F G) → ARITY F = length ys →
  (∀ x l, thesis F l x) → (∀ x l, thesis G l x) → ∃ s,
  « re_forward (ARITY F) (convert F) (convert G) »
    (↑y :: ↑↑ys ++ repeat 0 (anc (RE F G))) =
  ↑y::↑s::0::0::0::↑EVALUATE (RE F G) (y::ys)::↑y::↑↑ys++
    repeat 0 (anc (RE F G)-6).
Proof.
  intros. unfold re_forward. segment.
  asserts_rewrite (
    «id ‖ \seq (ARITY F) 6\» (↑y::↑↑ys++repeat 0 (anc (RE F G))) =
    ↑y::« \seq (ARITY F) 6\» (↑↑ys++repeat 0 (anc (RE F G)))).
  { reflexivity. }
  asserts_rewrite (
    «\seq (ARITY F) 6\» (↑↑ ys ++ repeat 0 (anc (RE F G))) =
    0::0::0::0::0::0::↑↑ys ++ repeat 0 (anc (RE F G)-6) ).
  { rewrite H0. rewrite <- (map_length Z.of_nat).
    rewrite perm_seq.
    rewrite repeat_splice. rewrite repeat_skipn.
    rewrite min_r. reflexivity. now apply anc_re_6.
    rewrite repeat_length. now apply anc_re_6. }
  asserts_rewrite (
    « Id 6 ‖ convert F »
     (↑y::0::0::0::0::0::0::↑↑ys++repeat 0 (anc (RE F G)-6)) =
    ↑y::0::0::0::0::0::«convert F» (0::↑↑ys++repeat 0 (anc (RE F G)-6)) ).
  { reflexivity. }
  asserts_rewrite (
    « convert F » (0 :: ↑↑ ys ++ repeat 0 (anc (RE F G) - 6)) =
    ↑EVALUATE F ys :: ↑↑ys ++ repeat 0 (anc (RE F G)-6) ).
  { apply thesis_le. apply H1.
    assert (H3:=anc_re_r H). lia.
    inverts H. easy. easy. }
  asserts_rewrite (
    «Id 5‖Sw» (↑y::0::0::0::0::0::↑EVALUATE F ys::↑↑ys++
               repeat 0 (anc (RE F G)-6)) =
    ↑y::0::0::0::0::↑EVALUATE F ys::0::↑↑ys++repeat 0 (anc (RE F G)-6) ).
  { reflexivity. }
  rewrite it_def. replace (↓(↑ y)) with y. induction y. 3:lia.
  - exists O. reflexivity.
  - rewrite iter_succ.
    destruct IHy. apply eq_tail in H3. rewrite H3.
    segment.
    asserts_rewrite (
      « Id 3 ‖ convert G»
      (↑x::0::0::0::↑ EVALUATE (RE F G) (y :: ys)::↑y::↑↑ys++
        repeat 0 (anc (RE F G)-6)) =
      ↑x::0::0::«convert G»
        (0::↑ EVALUATE (RE F G) (y :: ys)::↑y::↑↑ys++
        repeat 0 (anc (RE F G)-6)) ).
    { reflexivity. }
    asserts_rewrite (
      «convert G» (0::↑ EVALUATE (RE F G) (y::ys)::↑y::↑↑ys++
        repeat 0 (anc (RE F G)-6)) =
      ↑EVALUATE G (EVALUATE (RE F G) (y::ys)::y::ys)::
        ↑EVALUATE (RE F G) (y::ys)::↑y::↑↑ys++
        repeat 0 (anc (RE F G)-6) ).
    { replace
        (↑ EVALUATE (RE F G) (y :: ys) :: ↑ y :: ↑↑ ys ++
         repeat 0 (anc (RE F G) - 6))
      with (↑↑(EVALUATE (RE F G) (y::ys)::y::ys) ++
         repeat 0 (anc (RE F G) - 6)).
      apply thesis_le. easy.
      assert (h4:=anc_re_l H). lia.
      inverts H. easy.
      simpl. rewrite <- H0. inverts H. easy.
      easy. }
    asserts_rewrite (
      « Id 3 ‖ Sw » (↑ x:: 0:: 0::
        ↑ EVALUATE G (EVALUATE (RE F G) (y :: ys) :: y :: ys)::
        ↑ EVALUATE (RE F G) (y :: ys) :: ↑ y :: ↑↑ ys ++
        repeat 0 (anc (RE F G) - 6)) =
      ↑x::0::0::↑EVALUATE (RE F G) (y :: ys)::
        ↑EVALUATE G (EVALUATE (RE F G) (y :: ys)::y::ys)::
        ↑y::↑↑ys++repeat 0 (anc (RE F G)-6)).
    { reflexivity. }
    asserts_rewrite (
      «\[0;3]%nat\» (↑x::0::0::↑EVALUATE (RE F G) (y :: ys)::
        ↑EVALUATE G (EVALUATE (RE F G) (y :: ys)::y::ys)::
        ↑y::↑↑ys++repeat 0 (anc (RE F G)-6)) =
      ↑x::↑EVALUATE (RE F G) (y :: ys)::0::0::
        ↑EVALUATE G (EVALUATE (RE F G) (y :: ys)::y::ys)::
        ↑y::↑↑ys++repeat 0 (anc (RE F G)-6) ).
    { reflexivity. }
    exists (cp' x (EVALUATE (RE F G) (y :: ys))).
    f_equal.
    asserts_rewrite (
      «push» (↑x::↑ EVALUATE (RE F G) (y::ys)::0::0::
        ↑EVALUATE G (EVALUATE (RE F G) (y::ys)::y::ys)::
        ↑y::↑↑ys++repeat 0 (anc (RE F G)-6)) =
      ↑ cp' x (EVALUATE (RE F G) (y::ys))::0::0::0::
        ↑EVALUATE G (EVALUATE (RE F G) (y::ys)::y::ys)::
        ↑y::↑↑ys++repeat 0 (anc (RE F G)-6) ).
    { rewrite longer. simpl arity.
      simpl_splice. rewrite push_def. reflexivity. }
    asserts_rewrite (
      «Id 5 ‖ Su» (↑cp' x (EVALUATE (RE F G) (y :: ys))::
        0::0::0::↑ EVALUATE G (EVALUATE (RE F G) (y::ys)::y::ys)::
        ↑y::↑↑ys++repeat 0 (anc (RE F G)-6)) =
      ↑cp' x (EVALUATE (RE F G) (y :: ys))::
        0::0::0::↑ EVALUATE G (EVALUATE (RE F G) (y::ys)::y::ys)::
        ↑y+1::↑↑ys++repeat 0 (anc (RE F G)-6) ).
    { reflexivity. }
    f_equal. f_equal. f_equal. f_equal. f_equal.
    2:f_equal; lia.
    f_equal. unfold EVALUATE. fold EVALUATE.
    rewrite iter_succ. simpl.
    f_equal. f_equal. f_equal.
    + clear H3. induction y.
      * reflexivity.
      * simpl. rewrite <- IHy. reflexivity.
    + clear H3. induction y.
      * reflexivity.
      * simpl. rewrite <- IHy. reflexivity.
Qed.

Lemma thesis_re : ∀ F G l x,
  (∀ x l, thesis F l x) → (∀ x l, thesis G l x) →
  thesis (RE F G) l x.
Proof.
  intros. unfold thesis. intros.
  unfold convert. fold convert. segment.
  asserts_rewrite (
    (« id ‖ re_forward (ARITY F) (convert F) (convert G) »
      (x :: ↑↑ l ++ repeat 0 (anc (RE F G)))) =
    x :: «re_forward (ARITY F) (convert F) (convert G)»
      (↑↑ l ++ repeat 0 (anc (RE F G))) ).
  { rewrite pa_def. reflexivity. }
  assert (∃ y ys, l = y :: ys).
  { destruct l.
    - simpl in H2. lia.
    - exists n l. reflexivity. }
  destruct H3 as [y [ys H3]]. rewrite H3. simpl map.
  rewrite <- app_comm_cons.
  assert (∃ s,
    « re_forward (ARITY F) (convert F) (convert G) »
      (↑y :: ↑↑ys ++ repeat 0 (anc (RE F G))) =
    ↑y::↑s::0::0::0::↑EVALUATE (RE F G) l::↑y::↑↑ys++repeat 0 (anc (RE F G)-6)).
  { rewrite H3. apply re_forward_def.
    easy.
    rewrite H3 in H2. simpl in H2. lia.
    easy. easy. }
  destruct H4. rewrite H4.
  asserts_rewrite (
    «\[6;0]%nat\»(x::↑y::↑x0::0::0::0::↑EVALUATE (RE F G) l::↑y::↑↑ys++
                  repeat 0 (anc (RE F G)-6)) =
    ↑EVALUATE (RE F G) l::x::↑y::↑x0::0::0::0::↑y::↑↑ys++
      repeat 0 (anc (RE F G)-6) ).
  { reflexivity. }
  asserts_rewrite (
    «inc» (↑EVALUATE (RE F G) l::x::↑y::↑x0::0::0::0::↑y::↑↑ys++
            repeat 0 (anc (RE F G)-6)) =
    ↑EVALUATE (RE F G) l::x+↑EVALUATE (RE F G) l::↑y::↑x0::0::0::0::↑y::↑↑ys++
            repeat 0 (anc (RE F G)-6) ).
  { rewrite longer. simpl arity.
    asserts_rewrite (
      (↑ EVALUATE (RE F G) l::x::↑y::↑x0::0::0::0::↑y::↑↑ys++
       repeat 0 (anc (RE F G)-6))^[0, 2] =
      ↑EVALUATE (RE F G) l::x::[]).
    { reflexivity. }
    rewrite inc_def. reflexivity. lia. }
  asserts_rewrite (
    (« inv (\ [6%nat; 0%nat] \) »
     (↑ EVALUATE (RE F G) l::x+↑ EVALUATE (RE F G) l::↑y::↑x0
      ::0::0::0::↑y::↑↑ys++repeat 0 (anc (RE F G)-6))) =
    x+↑ EVALUATE (RE F G) l::↑y::↑x0::0::0::0::
      ↑EVALUATE (RE F G) l::↑y::↑↑ys++repeat 0 (anc (RE F G)-6)).
  { reflexivity. }
  asserts_rewrite (
    « id ‖ inv (re_forward (ARITY F) (convert F) (convert G)) »
    (x + ↑ EVALUATE (RE F G) l::↑y::↑x0::0::0::0::
      ↑EVALUATE (RE F G) l::↑y::↑↑ys++ repeat 0 (anc (RE F G)-6)) =
    x + ↑ EVALUATE (RE F G) l::
      «inv (re_forward (ARITY F) (convert F) (convert G))»
      (↑y::↑x0::0::0::0::
      ↑EVALUATE (RE F G) l::↑y::↑↑ys++ repeat 0 (anc (RE F G)-6))).
  { reflexivity. }
  f_equal. rewrite H3. reflexivity.
  rewrite <- proposition_1. apply H4.
Qed.

Open Scope nat.
Lemma anc_length_le_anc_co : ∀ F Gs, strict (CO F Gs) →
  anc F + length Gs ≤ anc (CO F Gs).
Proof.
  intros. unfold anc.
  assert (H':=H). inverts H'.
  simpl ARITY. apply Nat.le_add_le_sub_r.
  asserts_rewrite (
    arity (convert F) - (1 + ARITY F) + length Gs +
      (1 + list_max (map ARITY Gs)) =
    arity (convert F) + list_max (map ARITY Gs) ).
  { assert (H1:=ARITY_le_arity H2). lia. }
  rewrite convert_co_def. simpl ARITY.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. right.
  rewrite arity_pa_def. simpl. lia.
Qed.

Lemma co_load_le_anc_co : ∀ F Gs, strict (CO F Gs) →
  arity (co_loading (list_max (map ARITY Gs)) (map convert Gs)) -
    list_max (map ARITY Gs) ≤ anc (CO F Gs).
Proof.
  intros. unfold anc.
  assert (H':=H). inverts H'. simpl ARITY.
  asserts_rewrite (
    arity (convert (CO F Gs)) - (1 + list_max (map ARITY Gs)) =
    arity (convert (CO F Gs)) - 1 - list_max (map ARITY Gs) ).
  { lia. }
  apply Nat.sub_le_mono_r.
  apply Nat.le_add_le_sub_r.
  rewrite convert_co_def. simpl ARITY.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  rewrite arity_co_def. rewrite Nat.max_le_iff. left.
  simpl. lia.
Qed.

Lemma anc_lt_co_load : ∀ A Gs, strict A →
  ARITY A = list_max (map ARITY (A :: Gs))→
  anc A <
  arity (co_loading (list_max (map ARITY (A::Gs))) (map convert (A::Gs))) -
    list_max (map ARITY (A::Gs)).
Proof.
  intros. unfold anc. apply Nat.lt_add_lt_sub_r.
  asserts_rewrite (
    arity (convert A) - (1 + ARITY A) + list_max (map ARITY (A :: Gs)) =
    arity (convert A) - 1 ).
  { rewrite <- H0. assert(H6:=ARITY_le_arity H). lia. }
  simpl co_loading.
  rewrite arity_co_def. rewrite Nat.max_lt_iff. left.
  rewrite arity_co_def. rewrite Nat.max_lt_iff. right.
  assert(H':=ARITY_le_arity H). lia.
Qed.

Lemma arity_co_load_lt_arity_co_load : ∀ A Gs,
  Forall (λ G : PRF, ARITY G = list_max (map ARITY (A :: Gs))) (A :: Gs) →
  arity (co_loading (list_max (map ARITY Gs)) (map convert Gs)) -
    list_max (map ARITY Gs) <
  arity (co_loading (list_max (map ARITY (A::Gs))) (map convert (A::Gs))) -
    list_max (map ARITY (A::Gs)).
Proof.
  intros. destruct Gs.
  - simpl. rewrite arity_call. lia.
  - assert (H':=H).
    apply Forall_inv in H.
    apply Forall_inv_tail in H'. apply Forall_inv in H'.
    assert (ARITY A = list_max (map ARITY (p::Gs))).
    { simpl in *. lia. }
    remember (p::Gs) as Gs'.
    apply Nat.le_add_le_sub_l.
    simpl co_loading.
    rewrite arity_co_def. rewrite Nat.max_le_iff. right.
    simpl arity. rewrite <- H0.
    assert (ARITY A ≤ arity (co_loading (ARITY A) (map convert Gs'))).
    { subst. simpl. rewrite arity_call. lia. }
    simpl in *. rewrite Nat.max_id. rewrite max_l. lia. rewrite H. lia.
Qed.

Open Scope Z.
Lemma co_load_def : ∀ Gs n l,
  Forall (λ G : PRF, ∀ (x : Z) (l : list nat), thesis G l x) Gs →
  Forall (λ G : PRF, strict G) Gs →
  Forall (λ G : PRF, ARITY G = list_max (map ARITY Gs)) Gs →
  list_max (map ARITY Gs) = length l →
  arity ( co_loading (list_max (map ARITY Gs)) (map convert Gs) ) -
    list_max (map ARITY Gs) ≤ n →
  « co_loading (list_max (map ARITY Gs)) (map convert Gs) »
    (↑↑ l ++ repeat 0 n) =
  ↑↑ map (λ G : PRF, EVALUATE G l) Gs ++ ↑↑ l ++ repeat 0 (n - length Gs).
Proof.
  intros. gen n l. induction Gs.
  - intros. simpl. f_equal. f_equal. lia.
  - intros. simpl co_loading. segment.
    assert (list_max (map ARITY Gs) ≤ ARITY a).
    { apply Forall_inv in H1.
      rewrite H1. simpl. lia. }
    rewrite max_l in *. 2:easy.
    assert(ARITY a = length l).
    { rewrite <- H2. simpl. lia. }
    asserts_rewrite (
      « \ [ARITY a] \ » (↑↑ l ++ repeat 0 n) =
      0 :: ↑↑l ++ repeat 0 (n-1) ).
    { unfold perm. simpl call_list. rewrite Nat.add_0_r. simpl.
      apply Forall_inv in H1.
      rewrite call_def.
      replace ((↑↑ l ++ repeat 0 n) ^[ ARITY a])
      with [0].
      replace ((↑↑ l ++ repeat 0 n) ^[ 0, ARITY a])
      with (↑↑l).
      replace ((↑↑l ++ repeat 0 n) ^[ 1 + ARITY a, ∞ ])
      with (repeat 0 (n-1)).
      reflexivity.
      rewrite skipn_app. rewrite skipn_all2. rewrite app_nil_l.
      rewrite repeat_skipn. f_equal. f_equal. rewrite map_length.
      lia. rewrite map_length. lia.
      rewrite splice_app. rewrite splice_all. rewrite splice_gt.
      rewrite app_nil_r. reflexivity.
      rewrite map_length. lia. rewrite map_length. lia.
      rewrite splice_app. rewrite splice_all2. rewrite app_nil_l.
      rewrite map_length.
      replace (1 + ARITY a - length l)%nat with (1+(ARITY a - length l))%nat.
      replace (ARITY a - length l)%nat with O.
      rewrite splice_nth with (d:=0). f_equal.
      destruct n. reflexivity. reflexivity.
      rewrite repeat_length.
      apply Forall_inv in H0. assert(H':= anc_lt_co_load _ H0 H1). lia.
      lia. lia.
      rewrite map_length. lia.
      rewrite app_length. rewrite map_length.
      rewrite repeat_length.
      apply Forall_inv in H0. assert(H':= anc_lt_co_load _ H0 H1). lia. }
    rewrite thesis_le.
    rewrite pa_def. simpl. f_equal.
    destruct Gs. reflexivity.
    assert (ARITY a = ARITY p).
    { pose (Forall_inv H1) as H6. simpl in H6.
      pose (Forall_inv_tail H1) as H7.
      apply Forall_inv in H7. simpl in H7.
      lia. }
    assert (list_max (map ARITY (p :: Gs)) = ARITY a).
    { rewrite H6. apply Forall_inv_tail in H1.
      apply Forall_inv in H1. rewrite H1. simpl. lia. }
    remember (p::Gs) as Gs'.
    rewrite <- H7.
    replace (n - S (length Gs'))%nat with ((n - 1) - length Gs')%nat.
    apply IHGs.
    apply Forall_inv_tail in H. easy.
    apply Forall_inv_tail in H0. easy.
    assert (
      list_max (map ARITY Gs') = list_max (map ARITY (a :: Gs')) ).
    { simpl in *. lia. }
    apply Forall_inv_tail in H1. rewrite H8. easy.
    assert(H':=arity_co_load_lt_arity_co_load H1). simpl in *. lia.
    lia. lia.
    apply Forall_inv in H. easy.
    apply Forall_inv in H0. apply Forall_inv in H1.
    assert(H':= anc_lt_co_load _ H0 H1). lia.
    apply Forall_inv in H0. easy.
    apply Forall_inv in H1. lia.
Qed.

Lemma thesis_co : ∀ F Gs l x,
  (∀ x l, thesis F l x) → (Forall (λ G, ∀ x l, thesis G l x) Gs) →
  thesis (CO F Gs) l x.
Proof.
  intros. unfold thesis. intros.
  simpl convert. segment.
  asserts_rewrite (
    « id ‖ co_loading (list_max (map ARITY Gs)) (map convert Gs)»
      (x :: ↑↑ l ++ repeat 0 (anc (CO F Gs))) =
    x :: «co_loading (list_max (map ARITY Gs)) (map convert Gs)»
      (↑↑ l ++ repeat 0 (anc (CO F Gs))) ).
  { reflexivity. }
  assert (
    « co_loading (list_max (map ARITY Gs)) (map convert Gs) »
      (↑↑ l ++ repeat 0 (anc (CO F Gs))) =
    ↑↑map (λ G, EVALUATE G l) Gs ++ ↑↑l ++
      repeat 0%Z (anc (CO F Gs) - length Gs) ).
  { assert(H':= co_load_le_anc_co H1). inverts H1. apply co_load_def.
    easy. easy. easy. easy. lia. }
  rewrite H3.
  asserts_rewrite (
    « \ seq (S(length Gs)) (list_max (map ARITY Gs)) \ »
      (x:: ↑↑ map (λ G : PRF, EVALUATE G l) Gs ++
      ↑↑ l ++ repeat 0 (anc (CO F Gs) - length Gs)) =
    ↑↑l ++ x::↑↑map (λ G, EVALUATE G l) Gs ++
    repeat 0 (anc (CO F Gs) - length Gs) ).
  { rewrite app_comm_cons.
    remember (x:: ↑↑ map (λ G : PRF, EVALUATE G l) Gs) as l'.
    asserts_rewrite (S (length Gs) = length l').
    { subst. simpl. rewrite !map_length. reflexivity. }
    rewrite perm_seq.
    rewrite firstn_app_l. f_equal. subst.
    rewrite app_comm_cons. f_equal.
    rewrite skipn_app_l. reflexivity.
    rewrite map_length. simpl in H2. easy.
    rewrite map_length. simpl in H2. easy.
    rewrite app_length. rewrite map_length.
    rewrite repeat_length.
    replace (list_max (map ARITY Gs)) with (ARITY (CO F Gs)).
    2: reflexivity.
    rewrite H2.
    assert (H':=anc_length_le_anc_co H1). lia. }
  asserts_rewrite (
    « Id (list_max (map ARITY Gs)) ‖ convert F »
        (↑↑l++x::↑↑map (λ G : PRF, EVALUATE G l) Gs ++
        repeat 0 (anc (CO F Gs) - length Gs)) =
    ↑↑l ++ «convert F» (x::↑↑map (λ G : PRF, EVALUATE G l) Gs ++
        repeat 0 (anc (CO F Gs) - length Gs)) ).
  { simpl in H2. rewrite pa_def. rewrite firstn_app_l.
    rewrite id_def. f_equal. rewrite skipn_app_l.
    reflexivity. rewrite map_length. easy.
    rewrite map_length. easy. }
  asserts_rewrite (
    « convert F » (x:: ↑↑ map (λ G : PRF, EVALUATE G l) Gs ++
      repeat 0 (anc (CO F Gs) - length Gs)) =
    x+↑EVALUATE F (map (λ G : PRF, EVALUATE G l) Gs) ::
      ↑↑ map (λ G : PRF, EVALUATE G l) Gs ++
      repeat 0 (anc (CO F Gs) - length Gs) ).
  { assert (H':=anc_length_le_anc_co H1).
    inverts H1. apply thesis_le. easy.
    lia. easy. rewrite map_length. easy. }
  asserts_rewrite (
    « inv (\ seq (S (length Gs)) (list_max (map ARITY Gs)) \) »
      (↑↑ l ++ x + ↑ EVALUATE F (map (λ G : PRF, EVALUATE G l) Gs)::
      ↑↑ map (λ G : PRF, EVALUATE G l) Gs ++
      repeat 0 (anc (CO F Gs) - length Gs)) =
    x + ↑ EVALUATE F (map (λ G : PRF, EVALUATE G l) Gs) ::
      ↑↑ map (λ G : PRF, EVALUATE G l) Gs ++ ↑↑ l ++
      repeat 0 (anc (CO F Gs) - length Gs) ).
  { rewrite <- proposition_1.
    rewrite app_comm_cons.
    remember (x + ↑ EVALUATE F (map (λ G : PRF, EVALUATE G l) Gs)::
              ↑↑ map (λ G : PRF, EVALUATE G l) Gs) as l'.
    asserts_rewrite (S (length Gs) = length l').
    { subst. simpl. rewrite !map_length. reflexivity. }
    rewrite perm_seq.
    rewrite firstn_app_l. f_equal. subst.
    rewrite app_comm_cons. f_equal.
    rewrite skipn_app_l. reflexivity.
    rewrite map_length. simpl in H2. easy.
    rewrite map_length. simpl in H2. easy.
    rewrite app_length. rewrite map_length.
    rewrite repeat_length.
    replace (list_max (map ARITY Gs)) with (ARITY (CO F Gs)).
    2: reflexivity.
    rewrite H2.
    assert (H':=anc_length_le_anc_co H1). lia. }
  asserts_rewrite (
    «Id 1 ‖ inv (co_loading (list_max (map ARITY Gs)) (map convert Gs)) »
      (x + ↑ EVALUATE F (map (λ G : PRF, EVALUATE G l) Gs)::
      ↑↑ map (λ G : PRF, EVALUATE G l) Gs ++ ↑↑l ++
      repeat 0 (anc (CO F Gs) - length Gs)) =
    x + ↑ EVALUATE F (map (λ G : PRF, EVALUATE G l) Gs) ::
      «inv (co_loading (list_max (map ARITY Gs)) (map convert Gs))»
      (↑↑ map (λ G : PRF, EVALUATE G l) Gs ++ ↑↑ l ++
      repeat 0 (anc (CO F Gs) - length Gs)) ).
  { reflexivity. }
  asserts_rewrite (
    « inv (co_loading (list_max (map ARITY Gs)) (map convert Gs)) »
      (↑↑ map (λ G : PRF, EVALUATE G l) Gs ++ ↑↑ l ++
      repeat 0 (anc (CO F Gs) - length Gs)) =
    ↑↑ l ++ repeat 0 (anc (CO F Gs)) ).
  { rewrite <- proposition_1. apply H3. }
  reflexivity.
Qed.

Lemma list_max_ge : ∀ l n, In n l → n ≤ list_max l.
Proof.
  intros. induction l.
  - false.
  - simpl in *. destruct H.
    + subst. lia.
    + apply Nat.max_le_iff. right. apply IHl. easy.
Qed.

Lemma theorem_5_le : ∀ F l x d, depth F ≤ d → thesis F l x.
Proof.
  intros. gen F x l. induction d.
  - intro F. induction F; intros.
    + apply thesis_ze.
    + apply thesis_su.
    + apply thesis_pr.
    + simpl in H. lia.
    + simpl in H.
      apply thesis_re.
      apply IHF1. lia. apply IHF2. lia.
  - intro F. induction F; intros.
    + apply thesis_ze.
    + apply thesis_su.
    + apply thesis_pr.
    + simpl in H. apply thesis_co.
      apply IHd. simpl in H. lia.
      rewrite Forall_forall. intros. apply IHd.
      assert (depth x0 ≤ list_max (map depth Gs)).
      { apply list_max_ge. apply in_map. easy. }
      lia.
    + simpl in H.
      apply thesis_re.
      apply IHF1. lia. apply IHF2. lia.
Qed.

Theorem theorem_5 : ∀ F l x, thesis F l x.
Proof.
  intros. apply theorem_5_le with (d:=depth F). reflexivity.
Qed.