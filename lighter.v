Require Import Unicode.Utf8 List ZArith Lia.
Import ListNotations.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.
Set Implicit Arguments.

(* In questa versione RPP non è un dependent type, quindi non si ha ad esempio RPP 3, RPP 5... ma solo RPP. Tale indice è infatti ridondante: è possibile calcolare meccanicamente l'arità, grazie alla funzione arity. Non avere l'indice rende molto più facile definire funzioni che ritornano RPP di arità variabile.
Inoltre c'è Nu, la funzione RPP di arità 0. *)

Inductive RPP :=
  | Nu
  | Id
  | Ne
  | Su
  | Pr
  | Sw
  | Co (f g : RPP)
  | Pa (f g : RPP)
  | It (f : RPP)
  | If (f g h : RPP).

Notation "f ;; g" := (Co f g) (at level 65, left associativity).
(* \Vert ‖ *)
Notation "f ‖ g" := (Pa f g) (at level 65, left associativity).

Fixpoint inv f :=
  match f with
  | Nu => Nu
  | Id => Id
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
  | Nu => 0
  | Id => 1
  | Ne => 1
  | Su => 1
  | Pr => 1
  | Sw => 2
  | Co f g => max (arity f) (arity g)
  | Pa f g => arity f + arity g
  | It f => S (arity f)
  | If f g h => S (max (arity f) (max (arity g) (arity h)))
  end.

Lemma arity_inv : ∀ f, arity (inv f) = arity f.
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
  | Nu => l
  | Id => l
  | Ne => match l with []=>l | x::l' => -x :: l' end
  | Su => match l with []=>l | x::l' => x+1 :: l' end
  | Pr => match l with []=>l | x::l' => x-1 :: l' end
  | Sw => match l with x::y::l' => y::x::l' | _=>l end
  | Co f g => (evaluate g) (evaluate f l)
  | Pa f g => let n := arity f in
    evaluate f (firstn n l) ++ evaluate g (skipn n l)
  | It f => match l with []=>l
    | x::l' => x::iter (evaluate f) (Z.abs_nat x) l' end
  | If f g h => match l with []=>l
    | x::l' => match x with
      | Zpos p => x::(evaluate f) l'
      | Z0 => x::(evaluate g) l'
      | Zneg p => x::(evaluate h) l'
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
  - simpl. induction (Z.abs_nat z); auto. simpl. rewrite IHf; lia.
  - destruct z; simpl; congruence.
Qed.

(* La proposizione 2 ha una dimostrazione bruttina per il fatto che non c'è alcuna ipotesi sulla lunghezza di l. *)

Ltac liast :=
  try rewrite length_evaluate; try rewrite evaluate_nil;
  try rewrite firstn_length; try rewrite skipn_length;
  try rewrite app_nil_r;
  simpl; try lia; auto.

Theorem proposition_2 : ∀ f g f' g' l, arity f = arity g →
  «(f‖f');;(g‖g')» l = «(f;;g)‖(f';;g')» l.
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

Theorem proposition_1_l : ∀ f l, «f;;inv f» l = l.
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

Theorem proposition_1_r : ∀ f l, «inv f;;f» l = l.
Proof.
  intros. rewrite <- (inv_involute f) at 2. apply proposition_1_l.
Qed.

Fixpoint Id' n :=
  match n with
    | O => Nu
    | S n' => Id ‖ Id' n'
  end.

Lemma id'_identity : ∀ n l, «Id' n» l = l.
Proof.
  intros n. induction n. reflexivity.
  unfold Id'. fold Id'. simpl.
  destruct l; rewrite IHn; reflexivity.
Qed.

Lemma arity_id' : ∀ n, arity (Id' n) = n.
Proof. induction n; simpl; auto. Qed.

(* Ora viene definita perm: data ad esempio la lista [5;2;1;4], la funzione RPP perm [5;2;1;4] = \[6;4;1;5]\ ha l'effetto di portare il 6° elemento in 1° posizione, il 4° elemento in 2°, il 1° elemento in 3° e il 5° elemento in 4°, ponendo nelle posizioni successive tutti gli altri elementi.
Bisogna prima definire alcune funzioni ausiliarie. *)

Open Scope nat_scope.

(* Ho chiamato questa funzione w come weakening anche se ha un significato diverso rispetto all'originale: serve ad applicare la funzione f a partire dall'i-esima posizione (e non fa nulla se i=0). *)

Definition w n f :=
  match n with
  | O => Nu
  | S i => Id' i ‖ f
  end.

Definition Sw' i := w i Sw.

Fixpoint call i :=
  match i with
  | O => Nu
  | S j => Sw' j ;; call j
  end.

Fixpoint call_list l :=
  match l with
  | [] => Nu
  | i::l => call i ;; call_list l
  end.

Fixpoint prepare l :=
  match l with
  | [] => []
  | i :: l' => i + length (filter (λ j, i <? j) l') :: prepare l'
  end.

Definition perm l := call_list (rev (prepare l)).

Notation "\ l \" := (perm l) (at level 50).

Definition It' i l f := \i::l\ ;; It f ;; inv(\i::l\).
Definition If' i l f g h := \i::l\ ;; If f g h ;; inv(\i::l\).

Definition Su' i := w i Su.
Definition Pr' i := w i Pr.

(* La funzione cast forza l'arità n sulla funzione f *)

Definition cast n f :=
  match arity f <=? n with
  | true => f ‖ Id' (n - arity f)
  | false => Id' n
  end.

Lemma arity_cast : ∀ f n, arity (cast n f) = n.
Proof.
  intros. unfold cast.
  remember (arity f <=? n).
  destruct b.
  - simpl. rewrite arity_id'.
    apply le_plus_minus_r. apply Nat.leb_le. auto.
  - apply arity_id'.
Qed.

Definition Su'' i n := cast n (w i Su).

(* Si possono ora definire le funzioni descritte nell'articolo. *)

Definition inc j i := It' j [i] Su.
Definition dec j i := inv(inc j i).

(* La definizione originale di less mi sembra errata nel caso x_i < 0, x_j < 0, perciò anzichè un'unica same_sign ho scritto pos_sign e neg_sign. *)

Definition pos_sign := dec 2 3 ;; If' 3 [1;2] Su Id Id ;; inv (dec 2 3).
Definition neg_sign := dec 2 3 ;; If' 3 [1;2] Id Id Su ;; inv (dec 2 3).
Definition f_less := If' 5 [1;2;3;4]
  (If' 4 [1;2;3] pos_sign Su Su)
  (If' 4 [1;2;3] Id Id Su)
  (If' 4 [1;2;3] Id Id neg_sign).
Definition less i j p q k :=
  \[k;p;q;i;j]\ ;; inc 5 3 ;; inc 4 2 ;;
  f_less ;;
  inv (\[k;p;q;i;j]\ ;; inc 5 3 ;; inc 4 2).

(* La funzione mult nell'articolo sembra avere un piccolo errore, nel secondo If bisognerebbe avere <j,i> anzichè <i,j> *)

Definition mult k j i := It' k [i;j] (inc 2 1) ;;
  If' k [j;i] (If Id Id Ne) Id (If Ne Id Id).

Definition min F i j := let n := arity F in
  It' (n+4) [] (
    F ;;
    If' j [n+1;n+2;n+3] Id Id (If' 3 [] Id (inc 2 1) Id ;; Su' 3) ;;
    inv F ;;
    (Su'' i n ‖ Su' 2)
  ) ;;
  If' (n+3) [n+1;n+4] Id (inc 2 1) Id ;;
  inv(It' (n+4) [] (
    F ;;
    If' j [n+1;n+2;n+3] Id Id (Su' 3) ;;
    inv F ;;
    (Su'' i n ‖ Su' 2)
  )).


Definition t2 := Su ;; inc 1 2.
Definition t3 := It t2.
Definition cp := inc 1 2 ;; inc 1 4 ;; \[2;3;1;4]\ ;;
  t3 ;; dec 1 2 ;; \[4;1;3;2]\ ;; dec 1 2.
Definition h := (\[3;2;1;4]\ ;; t3) ;; dec 3 4 ;; inv (\[3;2;1;4]\ ;; t3).
Definition cu := \[4;2;3;1]\ ;; inc 4 8 ;; min h 3 4 ;; Pr' 5 ;;
  \[1;2;5;4;3]\ ;; h ;; dec 4 3 ;; \[8;4;3;2;5;6;7;1]\.


Definition z_clean := (Id' 2 ‖ cu) ;; dec 4 1 ;; dec 5 2 ;; inv (Id' 2 ‖ cu).
Definition push := cp ;;  z_clean ;; \[3;2;1]\.
Definition pop := inv push.

Open Scope Z_scope.

Compute «mult 3 2 1» [10;20;-15].
Compute «less 1 2 3 4 5» [-5;-3;0;0;2].
Compute «cp» [5;7;0;0].
Compute «cu» [83;0;0;0;0;0;0;0].
Compute «push» [5;7;0;0;0;0;0;0;0;0].





