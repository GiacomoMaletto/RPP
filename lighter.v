Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.
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
    evaluate f (firstn n l) ++ evaluate g (skipn n l)
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
  - simpl. rewrite firstn_nil. rewrite skipn_nil.
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
    rewrite <- app_length. rewrite firstn_skipn. reflexivity.
  - simpl. induction (Z.to_nat z); auto. simpl. rewrite IHf; lia.
  - destruct z; simpl; congruence.
Qed.

(* La proposizione 2 ha una dimostrazione bruttina per il fatto che non c'è alcuna ipotesi sulla lunghezza di l. *)

Ltac liast :=
  try rewrite length_evaluate; try rewrite evaluate_nil;
  try rewrite firstn_length; try rewrite skipn_length;
  try rewrite app_nil_r;
  simpl; try lia; auto.

Theorem proposition_2 : ∀ f g f' g' l, arity f = arity g →
  «f‖f';;g‖g'» l = «(f;;g)‖(f';;g')» l.
Proof.
  intros. simpl.
  rewrite firstn_app. rewrite skipn_app.
  rewrite length_evaluate.
  remember (arity f) as n. rewrite <- H.
  replace (Init.Nat.max n n) with n; try lia.
  destruct (Nat.le_ge_cases (length l) n).
  - rewrite !firstn_all2. rewrite !skipn_all2.
    rewrite !evaluate_nil. rewrite !app_nil_r. reflexivity.
    all : liast.
  - assert (length (firstn n l) = n). liast. rewrite H1.
    asserts_rewrite (n - n = 0)%nat. lia.
    replace (firstn n _) with (« f » (firstn n l)).
    replace (skipn n (« f » (firstn n l))) with ([]:list Z).
    rewrite firstn_O. rewrite skipn_O. liast.
    rewrite skipn_all2; liast.
    remember (« f » (firstn n l)).
    rewrite firstn_all2; subst; liast.
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
  | 1 => Id O
  | 2 => Sw
  | S j => Id (j - 1) ‖ Sw ;; call j
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

Lemma ev_co_def : ∀ f g l, «f;;g» l = «g» («f» l).
Proof. reflexivity. Qed.

Lemma skipn_Sn : ∀ X n (l : list X), skipn (S n) l = tl (skipn n l).
Proof.
  intros. gen l. induction n.
  - reflexivity.
  - intros. destruct l.
    + reflexivity.
    + rewrite skipn_cons. rewrite IHn. reflexivity.
Qed.

Open Scope nat.
Lemma skipn_skipn : ∀ X n m (l : list X), skipn n (skipn m l) = skipn (n + m) l.
Proof.
  intros. gen l. induction n.
  - reflexivity.
  - intros. change (S n + m) with (S (n + m)).
    rewrite !skipn_Sn. rewrite IHn. reflexivity.
Qed.

Lemma firstn_ev : ∀ f n l, arity f ≤ n →
  firstn n («f» l) = «f» (firstn n l).
Proof.
  intros. gen n l. induction f.
  - reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct n. simpl in H. lia.
    destruct l. reflexivity. destruct l.
    reflexivity. reflexivity.
  - intros. simpl in *.
    rewrite IHf2. rewrite IHf1.
    reflexivity. lia. lia.
  - intros.
    destruct (Nat.le_ge_cases (length («f1» l)) (arity f1)).
    rewrite length_evaluate in H0. simpl in H.
    rewrite !firstn_all2. reflexivity. lia.
    rewrite length_evaluate. lia.
    simpl in *. rewrite <- IHf1.
    rewrite firstn_app. rewrite !firstn_firstn.
    rewrite min_r. rewrite min_l.
    rewrite IHf2. rewrite firstn_skipn_comm.
    rewrite firstn_length. rewrite min_l.
    replace (arity f1 + (n - arity f1)) with n.
    rewrite IHf1. reflexivity.
    lia. lia. auto. rewrite firstn_length. rewrite min_l.
    lia. auto. lia. lia. reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. simpl in *. f_equal.
    induction (Z.to_nat z). reflexivity.
    simpl. rewrite IHf. rewrite IHn0. reflexivity. lia.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. simpl in *.
    destruct z. rewrite IHf2. reflexivity. lia.
    rewrite IHf1. reflexivity. lia.
    rewrite IHf3. reflexivity. lia.
Qed.

Lemma skipn_ev : ∀ f n l, arity f ≤ n →
  skipn n («f» l) = skipn n l.
Proof.
  intros. gen n l. induction f.
  - reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. reflexivity.
  - intros. destruct n. simpl in H. lia.
    destruct n. simpl in H. lia.
    destruct l. reflexivity. destruct l.
    reflexivity. reflexivity.
  - intros. simpl in *.
    rewrite IHf2. rewrite IHf1.
    reflexivity. lia. lia.
  - intros.
    destruct (Nat.le_ge_cases (length l) (arity f1)).
    simpl in H.
    rewrite !skipn_all2. reflexivity. lia.
    rewrite length_evaluate. lia.
    intros. simpl in *. rewrite skipn_app.
    rewrite IHf1. rewrite skipn_all2. rewrite IHf2.
    rewrite skipn_skipn.
    asserts_rewrite
      (n-length («f1»(firstn(arity f1)l))+arity f1 = n).
    rewrite length_evaluate. rewrite firstn_length.
    rewrite min_l. lia. auto. auto.
    rewrite length_evaluate. rewrite firstn_length.
    rewrite min_l. lia. auto. rewrite firstn_length.
    rewrite min_l. lia. auto. lia.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. simpl in *.
    induction (Z.to_nat z). reflexivity.
    simpl. rewrite IHf. rewrite IHn0. reflexivity. lia.
  - intros. destruct n. simpl in H. lia.
    destruct l. reflexivity. simpl in *.
    destruct z. rewrite IHf2. reflexivity. lia.
    rewrite IHf1. reflexivity. lia.
    rewrite IHf3. reflexivity. lia.
Qed.

Lemma longer : ∀ f l,
  «f» l = «f» (firstn (arity f) l) ++ skipn (arity f) l.
Proof.
  intros. rewrite <- firstn_ev. rewrite <- (skipn_ev f).
  rewrite firstn_skipn. reflexivity. auto. auto.
Qed.

Definition ifzsw :=
  If inc id id ;; \[3;2;1]\ ;;
  If id Sw id ;; dec ;; \[3;1;2]\.

Open Scope Z.
Lemma ifzsw_z : ∀ n, «ifzsw» [0;n;0] = [n;0;0].
Proof. unfold ifzsw. reflexivity. Qed.

Notation Zp := Zpos.
Notation Zn := Zneg.

Lemma ifzsw_p : ∀ p q, «ifzsw» [Zp p; Zp q; 0] = [Zp p; Zp q; 0].
Proof.
  intros. unfold ifzsw. repeat rewrite ev_co_def.
  asserts_rewrite
    («If inc id id» [Zp p; Zp q; 0] = [Zp p; Zp q; Zp q]).
  { unfold evaluate. fold evaluate. rewrite inc_def. intuition. lia. }
  asserts_rewrite
    («\[3;2;1]%nat\» [Zp p; Zp q; Zp q] = [Zp q; Zp q; Zp p]).
  { reflexivity. }
  asserts_rewrite
    («If id Sw id» [Zp q; Zp q; Zp p] = [Zp q; Zp q; Zp p]).
  { reflexivity. }
  asserts_rewrite
    («dec» [Zp q; Zp q; Zp p] = [Zp q; 0; Zp p]).
  { rewrite longer. simpl firstn. simpl skipn. rewrite dec_def.
    unfold app. repeat f_equal. lia. lia. }
  reflexivity.
Qed.

Open Scope nat.

Definition cu_step := id ‖ Su ;; If id Su id ;; ifzsw ;; Pr.

Definition cu :=
  It cu_step ;; id ‖ Sw.

Definition tr := It (Su;; inc).

Definition cp :=
  inc ;; id ‖ (tr ;; dec) ;; dec ;;
  \[1;4;2]\ ;; inc ;; \[1;3;2]\.

(* \dow ↓ *)
Notation "↓ n" := (Z.to_nat n) (at level 20).
(* \upa ↑ *)
Notation "↑ n" := (Z.of_nat n) (at level 20).

Definition cp' (n m : nat) := (list_sum (seq 1 (n+m)) + n).
Open Scope Z.

Ltac partial := rewrite longer; simpl firstn; simpl skipn.
Ltac segment := repeat rewrite ev_co_def.
Ltac equal_list := auto; repeat f_equal; lia.

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
    replace (↑n + 1) with (↑(S n)). rewrite up_add. auto.
    lia. lia.
Qed.

Lemma cp_def : ∀ n m : nat,
  «cp» [↑n; ↑m; 0; 0] = [↑n; ↑m; ↑(cp' n m); 0].
Proof.
  intros. unfold cp. segment.
  asserts_rewrite (
    « inc » [↑ n; ↑ m; 0; 0] = [↑ n; ↑ m + ↑ n; 0; 0]).
  { partial.
    rewrite inc_def. auto. lia. }
  asserts_rewrite (↑m + ↑n = ↑n + ↑m). lia.
  asserts_rewrite (
    «id ‖ (tr;; dec)» [↑n;↑n + ↑m;0;0] =
    ↑n :: («tr;; dec» [↑n + ↑m;0;0]) ).
  { reflexivity. }
  rewrite ev_co_def.
  asserts_rewrite (
    «tr» [↑n+↑m; 0; 0] =
    [↑n+↑m; ↑n+↑m; ↑list_sum (seq 1 (n+m))] ).
  { rewrite up_add. apply tr_def. }
  asserts_rewrite (
    «dec» [↑n+↑m; ↑n+↑m; ↑list_sum (seq 1 (n+m))] =
    [↑n+↑m; 0; ↑list_sum (seq 1 (n+m))] ).
  { partial.
    rewrite dec_def.
    replace (↑n+↑m - (↑n+↑m)) with 0.
    auto. lia. lia. }
  asserts_rewrite (
    «dec» [↑n; ↑n+↑m; 0; ↑list_sum (seq 1 (n + m))] =
    [↑n; ↑m; 0; ↑list_sum (seq 1 (n + m))] ).
  { partial.
    rewrite dec_def. replace (↑n+↑m-↑n) with (↑m).
    auto. lia. lia. }
  asserts_rewrite (
    «\[1;4;2]%nat\» [↑n; ↑m; 0; ↑list_sum (seq 1 (n+m))] =
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

Definition push := cp ;; \[3;1;2]%nat\ ;; inv cu.
Definition pop := inv push.

Lemma push_def : ∀ n m,
  «push» [↑n; ↑m; 0; 0] = [↑cp' n m; 0; 0; 0].
Proof.
  intros. unfold push. segment.
  rewrite cp_def.
  simpl («\[3;1;2]%nat\» [↑n; ↑m; ↑cp' n m; 0]).
  rewrite <- proposition_1. rewrite cu_def. reflexivity.
Qed.










