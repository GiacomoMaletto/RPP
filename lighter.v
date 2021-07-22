Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.
Require Import splice.
Set Implicit Arguments.

(* In questa versione RPP non è un dependent type, quindi non si ha ad esempio RPP 3, RPP 5... ma solo RPP. Tale indice è infatti ridondante: è possibile calcolare meccanicamente l'arità, grazie alla funzione arity. Non avere l'indice rende molto più facile definire funzioni che ritornano RPP di arità variabile.
Inoltre c'è Nu, la funzione RPP di arità 0. *)

Inductive RPP :=
  | Id (n : nat)
  | Ne
  | Su
  | Pr
  | Sw
  | Co (f g : RPP)
  | Pa (f g : RPP)
  | It (f : RPP)
  | If (f g h : RPP).

Notation "f ;; g" := (Co f g) (at level 66, left associativity).
(* \Vert ‖ *)
Notation "f ‖ g" := (Pa f g) (at level 65, left associativity).

Fixpoint inv f :=
  match f with
  | Id n => Id n
  | Ne => Ne
  | Su => Pr
  | Pr => Su
  | Sw => Sw
  | Co f g => Co (inv g) (inv f)
  | Pa f g => Pa (inv f) (inv g)
  | It f => It (inv f)
  | If f g h => If (inv f) (inv g) (inv h)
  end.

Lemma inv_involute : ∀ f, inv (inv f) = f.
Proof. induction f; try constructor; simpl; congruence. Qed.

(* Notare che è possibile comporre funzioni di arità diverse: non è una grande differenza rispetto alle RPP originali, in effetti se si hanno arità diverse si può immaginare di applicare la funzione cast definita più avanti. *)

Fixpoint arity f :=
  match f with
  | Id n => n
  | Ne => 1
  | Su => 1
  | Pr => 1
  | Sw => 2
  | Co f g => max (arity f) (arity g)
  | Pa f g => arity f + arity g
  | It f => S (arity f)
  | If f g h => S (max (arity f) (max (arity g) (arity h)))
  end.

Lemma arity_inv : ∀  f, arity (inv f) = arity f.
Proof. induction f; auto; simpl; lia. Qed.

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

Open Scope Z_scope.

(* C'è una differenza con la definizione di RPP originale: It e If non controllano l'ultimo elemento ma il primo. Questo rende i calcoli e le dimostrazioni più semplici *)

(* Quando si applica ad esempio una RPP di arità 5 ad una lista, non è mai richiesto che tale lista abbia lunghezza 5: se ha lunghezza maggiore semplicemente verranno usati solo i primi 5 elementi e gli altri resteranno invariati, se la lunghezza è minore di 5 succederanno cose strane. Comunque nessun teorema che segue ha bisogno dell'ipotesi che la lista della lunghezza sia uguale all'arità. *)

Fixpoint evaluate f (l : list Z) : list Z :=
  match f with
  | Id n => l
  | Ne => match l with []=>[] | x::l' => -x::l' end
  | Su => match l with []=>[] | x::l' => x+1::l' end
  | Pr => match l with []=>[] | x::l' => x-1::l' end
  | Sw => match l with x::y::l' => y::x::l' | _=>l end
  | Co f g => (evaluate g) (evaluate f l)
  | Pa f g => let n := arity f in
    evaluate f (l^[0,n]) ++ evaluate g (l^[n,∞])
  | It f => match l with []=>[]
    | x::l' => x::iter (evaluate f) (Z.to_nat x) l' end
  | If f g h => match l with []=>[]
    | x::l' => match x with
      | Zpos _ => x::evaluate f l'
      | Z0 => x::evaluate g l'
      | Zneg _ => x::evaluate h l'
      end
    end
  end.

(* \laq « f » \raq *)
Notation "« f »" := (evaluate f).

(* Un piccolo esempio. *)
Compute «It Su» [-10;4].

Lemma evaluate_nil : ∀ f, «f» [] = [].
Proof.
  induction f; try reflexivity.
  - simpl. congruence.
  - simpl. rewrite splice_nil. rewrite skipn_nil.
    rewrite IHf1. rewrite IHf2. reflexivity.
Qed.

(* Tattica utile per il caso l=[] *)

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

(* La proposizione 2 ha una dimostrazione bruttina per il fatto che non c'è alcuna ipotesi sulla lunghezza di l. *)

Ltac liast := simpl in *;
  try rewrite !evaluate_nil; try rewrite !app_nil_r;
  try rewrite !app_length; try rewrite !length_evaluate;
  try rewrite !splice_length; try rewrite !skipn_length;
  try lia; try reflexivity.

Lemma id_def : ∀ n l, «Id n» l = l.
Proof. reflexivity. Qed.

Lemma su_def : ∀ n l, «Su» (n :: l) = n + 1 :: l.
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

Open Scope nat.
Fixpoint call i :=
  match i with
  | O => Id O
  | S j => Id j ‖ Sw ;; call j
  end.
Fixpoint call_list l :=
  match l with
  | [] => Id O
  | i::[] => call i
  | i::l => call i ;; call_list l
  end.
Fixpoint prepare l :=
  match l with
  | [] => []
  | i :: l' => i + length (filter (λ j, i <? j) l') :: prepare l'
  end.
Definition perm l := call_list (rev (prepare l)).
Notation "\ l \" := (perm l) (at level 50).

Definition id := Id 1.
Definition inc := It Su.
Definition dec := inv inc.

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

Lemma ev_it : ∀ f x y, «It f» (x::y) = x :: iter «f» (Z.to_nat x) y.
Proof. reflexivity. Qed.

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

Open Scope nat.
Definition ifzsw :=
  If inc id id ;; \[2;1;0]\ ;;
  If id Sw id ;; dec ;; \[2;0;1]\.

Open Scope Z.
Lemma ifzsw_z : ∀ n, «ifzsw» [0;n;0] = [n;0;0].
Proof. unfold ifzsw. reflexivity. Qed.

Notation Zp := Zpos.
Notation Zn := Zneg.

Ltac partial := rewrite longer; simpl_splice.
Ltac segment := repeat rewrite co_def.
Ltac equal_list := unfold app; auto; repeat f_equal; lia.

Lemma ifzsw_p : ∀ p q, «ifzsw» [Zp p; Zp q; 0] = [Zp p; Zp q; 0].
Proof.
  intros. unfold ifzsw. repeat rewrite co_def.
  asserts_rewrite
    («If inc id id» [Zp p; Zp q; 0] = [Zp p; Zp q; Zp q]).
  { rewrite if_def. rewrite inc_def. all: liast. }
  simpl («\[2;1;0]%nat\» [Zp p; Zp q; Zp q]).
  simpl («If id Sw id» [Zp q; Zp q; Zp p]).
  asserts_rewrite
    («dec» [Zp q; Zp q; Zp p] = [Zp q; 0; Zp p]).
  { partial. rewrite dec_def. equal_list. liast. }
  reflexivity.
Qed.

Open Scope nat.
Definition cu_step := id ‖ Su ;; If id Su id ;; ifzsw ;; Pr.

Definition cu :=
  It cu_step ;; id ‖ Sw.

Definition tr := It (Su;; inc).

Definition cp :=
  inc ;; id ‖ (tr ;; dec) ;; dec ;;
  \[0;3;1]\ ;; inc ;; \[0;2;1]\.

(* \dow ↓ *)
Notation "↓ n" := (Z.to_nat n) (at level 20).
(* \upa ↑ *)
Notation "↑ n" := (Z.of_nat n) (at level 20).

Definition cp' (n m : nat) := (list_sum (seq 1 (n+m)) + n).
Open Scope Z.


Open Scope nat.
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
  match n with
  | O => O
  | _ => S m
  end.

Definition cu'_snd (n m : nat) :=
  match n with
  | O => S m
  | _ => pred n
  end.

Definition cu'_pair p :=
  match p with (n, m) => (cu'_fst n m, cu'_snd n m) end.
Definition cu' i := iter cu'_pair i (O, O).

Lemma gt0_positive : ∀ n : Z, 0 < n → ∃ p : positive, n = Zp p.
Proof.
  intros. destruct n; try discriminate. eauto.
Qed.

Lemma cu_step_def : ∀ n m,
  «cu_step» [↑n; ↑m; 0] = [↑cu'_snd n m; ↑cu'_fst n m; 0].
Proof.
  intros. destruct n.
  - simpl. f_equal. lia.
  - unfold cu_step. segment.
    asserts_rewrite (
      « id ‖ Su » [↑ S n; ↑ m; 0] = [↑ S n; ↑m + 1; 0]).
    { reflexivity. }
    asserts_rewrite (
      « If id Su id » [↑ S n; ↑ m + 1; 0] = [↑ S n; ↑ m + 1; 0]).
    { reflexivity. }
    assert(∃ p, ↑m + 1 = Zp p). { eapply gt0_positive. lia. }
    assert(∃ q, ↑S n = Zp q). { eapply gt0_positive. lia. }
    destruct H. rewrite H. destruct H0. rewrite H0.
    rewrite ifzsw_p. rewrite <- H. rewrite <- H0.
    asserts_rewrite (
      « Pr » [↑ S n; ↑ m + 1; 0] = [↑ S n - 1; ↑m + 1; 0]).
    { reflexivity. }
    unfold cu'_fst. unfold cu'_snd.
    repeat f_equal. lia. lia.
Qed.

Lemma cu_step_z : ∀ m,
  «cu_step» [0; ↑m; 0] = [↑m + 1; 0; 0].
Proof.
  intros. replace 0 with (↑O). rewrite cu_step_def.
  simpl. equal_list. reflexivity.
Qed.

Lemma cu_step_p : ∀ n m, (O < n)%nat →
  «cu_step» [↑n; ↑m; 0] = [↑n - 1; ↑m + 1; 0].
Proof.
  intros. rewrite cu_step_def. f_equal.
  - unfold cu'_snd.
    assert(∃ n', n = S n').
    destruct n. lia. eauto. destruct H0. subst.
    lia.
  - unfold cu'_fst.
    assert(∃ n', n = S n').
    destruct n. lia. eauto. destruct H0. subst.
    equal_list.
Qed.

Lemma cu_step_le : ∀ n m k, k ≤ n →
  iter «cu_step» k [↑n; ↑m; 0] = [↑n - ↑k; ↑m + ↑k; 0].
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
  iter «cu_step» (cp' n m) [0; 0; 0] = [↑m; ↑n; 0] →
  iter «cu_step» (cp' (S n) m) [0; 0; 0] = [↑m; ↑n + 1; 0].
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
  iter «cu_step» (cp' n m) [0; 0; 0] = [↑m; ↑n; 0] →
  iter «cu_step» (cp' n (S m)) [0; 0; 0] = [↑m + 1; ↑n; 0].
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
  iter «cu_step» (cp' n m) [0; 0; 0] = [↑m; ↑n; 0].
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
  unfold cu. segment. rewrite ev_it. rewrite Nat2Z.id.
  rewrite cu_def_iter. reflexivity.
Qed.

Definition push := cp ;; \[2;0;1]%nat\ ;; inv cu.
Definition pop := inv push.

Lemma push_def : ∀ n m,
  «push» [↑n; ↑m; 0; 0] = [↑cp' n m; 0; 0; 0].
Proof.
  intros. unfold push. segment.
  rewrite cp_def.
  simpl («\[2;0;1]%nat\» [↑n; ↑m; ↑cp' n m; 0]).
  rewrite <- proposition_1. rewrite cu_def. reflexivity.
Qed.

Open Scope nat.

Inductive PRF :=
  | ZE (n : nat)
  | SU (i n : nat)
  | PR (i n : nat)
  | CO (F : PRF) (Gs : list PRF)
  | RE (F G : PRF).

Fixpoint ARITY (F : PRF) : nat :=
  match F with
  | ZE n | SU _ n | PR _ n => n
  | CO F Gs => list_max (map ARITY Gs)
  | RE F G => S (ARITY F)
  end.

Fixpoint EVALUATE F (l : list nat) : nat :=
  match F with
  | ZE n => 0
  | SU i n => S (nth i l 0)
  | PR i n => nth i l 0
  | CO F Gs => EVALUATE F (map (λ G, EVALUATE G l) Gs)
  | RE F G => match l with []=>0
    | n::l' => fst (fst (iter
      (λ p, match p with (a,x,y) => (EVALUATE G (a::x::y), S x, y) end)
      n
      (EVALUATE F l', 0, l')))
    end
  end.

Definition ADD := RE (PR 0 1) (CO (SU 0 1) [PR 0 3]).
Compute EVALUATE ADD [3;4].

Definition conv_su i n :=
  Id n ;; Su ;; \[S i; 0]\ ;; inc ;; inv(\[S i; 0]\).

Notation "↑↑ l" := (map Z.of_nat l) (at level 20).

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
    rewrite !splice_same. rewrite !app_nil_l.
    rewrite !app_assoc. rewrite !app_splice'.
    rewrite splice_app_skipn'.
    replace (n-(1+n-1))%nat with O. reflexivity. all: try lia.

Qed.

Lemma cons_app : ∀ X (x : X) l, x::l = [x]++l.
Proof. reflexivity. Qed.

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
  (map f l)^[a,b] = map f (l^[a,b]).
Proof.
  intros. unfold splice.
  rewrite map_firstn. rewrite map_skipn.
  reflexivity.
Qed.

Lemma conv_su_def : ∀ i n l x, length l = n → (i < n)%nat →
  «conv_su i n» (x::↑↑l) = x + ↑ S (nth i l O) :: ↑↑l.
Proof.
  intros. unfold conv_su. segment.
  rewrite id_def. rewrite su_def. rewrite perm1.
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
  
  \S i; 1\ (x+1 :: l) =
  nth (S i) l :: x+1 :: part 1 (S i) l ++ skipn (S (S i)) l


Lemma nth_Sn : ∀ X n (l : list X) d,
  nth (S n) l d = nth n (tail l) d.
Proof.
  intros. destruct l.
  - simpl. destruct n; reflexivity.
  - reflexivity.
Qed.


Open Scope nat.
Lemma firstn_Sn : ∀ X n (l : list X) d, n < length l →
  firstn (1+n) l = firstn n l ++ [nth n l d].
Proof.
  intros. lets (l0 & l1 & H0 & H1) : nth_split d H.
  rewrite H0. rewrite !firstn_app.
  rewrite firstn_all2.
  replace (1 + n - length l0) with (S (n - length l0)).
  rewrite firstn_cons.
  replace (n - length l0) with 0. simpl.
  rewrite <- H1. rewrite nth_middle. rewrite firstn_all2.
  f_equal. rewrite app_nil_r. reflexivity. all:lia.
Qed.

Open Scope nat.
Lemma nth_sum : ∀ X n m (l : list X) d,
  nth (n+m) l d = nth n (skipn m l) d.
Proof.
  intros. gen l. induction m.
  - intros. simpl. f_equal. auto.
  - intros. replace (n + S m) with (S (n + m)).
    rewrite nth_Sn. rewrite IHm.
    destruct l. simpl. rewrite skipn_nil.
    destruct n; auto. reflexivity. lia.
Qed.


Fixpoint co_loading n m gs :=
  match gs with
  | [] => Id 0
  | g::gs' => Id n ‖ (\[m]\ ;; g) ;; co_loading (S n) m gs'
  end.







Fixpoint convert (F : PRF) : RPP :=
  match F with
  | ZE n => Id n
  | SU i n => su i n
  | PR i n => \[1+i;1]\ ;; inc ;; inv(\[1+i;1]\) ‖ Id (n - i)
  | CO F Gs => let (n, m) := (ARITY (CO F Gs), length Gs) in

    co_loading 1 (1+n) (map convert Gs) ;;
    \seq (2+m) n\ ;;

    Id n ‖ (convert F) ;;

    inv (co_loading 1 (1+n) (map convert Gs) ;;
    \seq (2+m) n\)

  | RE F G => let n := ARITY (RE F G) in

    Id 2 ‖ \seq n 6\ ;;
    Id 7 ‖ convert F ;;
    Id 6 ‖ Sw ;;
    Id 1 ‖ It (Id 3 ‖ (convert G ;; Sw) ;; \[1;4]\ ;; push ;; Id 5 ‖ Su) ;;
    \[7;1]\ ;;

    inc ;;

    inv (Id 2 ‖ \seq n 6\ ;;
    Id 7 ‖ convert F ;;
    Id 6 ‖ Sw ;;
    Id 1 ‖ It (Id 3 ‖ (convert G ;; Sw) ;; \[1;4]\ ;; push ;; Id 5 ‖ Su) ;;
    \[7;1]\)
  end.



Definition anc F := pred (arity (convert F) - ARITY F).

Definition zeros n := repeat 0%Z n.

Open Scope Z.

Definition thesis F l x := ARITY F = length l →
  «convert F» (x :: ↑↑l ++ zeros (anc F)) =
  x + ↑(EVALUATE F l) :: ↑↑l ++ zeros (anc F).

Goal ∀ n l x, thesis (ZE n) l x.
Proof.
  unfold thesis. simpl. intros. equal_list.
Qed.

Goal ∀ i n l x, thesis (SU i n) l x.
Proof.
  unfold thesis. intros. unfold convert. simpl. f_equal.
Qed.

Theorem theorem_5 : ∀ F l x, thesis F l x.
Admitted.



Definition ADD := RE (PR 1 1) (CO (SU 1 1) [PR 1 3]).

Compute «convert ADD» (0 :: ↑↑[3;4]%nat ++ zeros (anc ADD)).
Compute 0 + ↑(EVALUATE ADD [3;4]%nat) :: ↑↑[3;4]%nat ++ zeros (anc ADD).
Compute arity (convert ADD).
Compute (1 + 2 + anc ADD)%nat.

Definition pad f l :=
  evaluate f (l ++ repeat 0%Z (arity f - length l)).


Lemma perm1 : ∀ n x l, (n < length l)%nat → «\[1+n;0]%nat\» (x::l) =
  l^[n] ++ x :: l^[0,n] ++ l^[1+n,∞].
Proof.
  intros. unfold perm. simpl prepare. simpl rev.
  replace (n+0)%nat with n. remember (S n) as m. simpl call_list.
  segment. rewrite id_def. rewrite call_def. subst. all: liast.
Qed.






