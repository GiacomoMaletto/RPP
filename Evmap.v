Require Import Unicode.Utf8 ZArith List String Lia FunctionalExtensionality.
(* https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html *)
Require Import LibTactics.

Set Implicit Arguments.

Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope string_scope.

(* RPPM lavora con mappe (funzione string → Z) anzichè liste. Per come è fatto, la composizione parallela e lo swap non servono. *)

Inductive RPPM : Type :=
  | Id
  | Ne (x : string)
  | Su (x : string)
  | Pr (x : string)
  | Co (f g : RPPM)
  | It (x : string) (f : RPPM)
  | If (x : string) (f g h : RPPM).

Notation "f ;; g" := (Co f g) (at level 65, left associativity).

Definition inc x y := It y (Su x).
Check inc.
Check inc "x" "y".

Fixpoint inv (f : RPPM) : RPPM :=
  match f with
  | Id => Id
  | Ne x => Ne x
  | Su x => Pr x
  | Pr x => Su x
  | Co f g => Co (inv g) (inv f)
  | It x f => It x (inv f)
  | If x f g h => If x (inv f) (inv g) (inv h)
  end.

Definition dec x y := inv (inc x y).

Lemma inv_involute : ∀ f, inv (inv f) = f.
Proof.
  intros. induction f; try reflexivity; simpl; congruence.
Qed.

Definition state := string → Z.

Definition empty : state := λ _, 0.
Definition update (st : state) x o : state :=
  λ y, if x =? y then o else st y.

(* \map ↦ *)
Notation "x ↦ n ; st" := (update st x n)
  (at level 100, n at next level, right associativity).
Notation "x ↦ n" := (update empty x  n)
  (at level 100).

(* Esempio di state *)
Compute ("x"↦30; "y"↦-5) "y".

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | O => x
  | S n => f (iter f n x)
  end.

Fixpoint evaluate (f : RPPM) (st : state) : state :=
  match f with
  | Id => st
  | Ne x => x ↦ -(st x); st
  | Su x => x ↦ st x + 1; st
  | Pr x => x ↦ st x - 1; st
  | Co f g => (evaluate g) (evaluate f st)
  | It x f => iter (evaluate f) (Z.abs_nat (st x)) st
  | If x f g h => evaluate (match st x with
    | Zpos _ => f
    | Z0 => g
    | Zneg _ => h
    end) st
  end.

(* \laq « f » \raq *)
Notation "« f »" := (evaluate f).

Compute «inc "x" "y"» ("x"↦30; "y"↦-5) "x".
Compute «dec "x" "y"» ("x"↦8; "y"↦-10) "x".

(* Attenzione! Non ogni programma RPPM è davvero reversibile. *)

Definition not_rev_example := It "x" (Pr "x").

(* not_rev_example azzera il valore di x, chiaramente non è reversibile. *)

Compute «not_rev_example» ("x"↦10) "x".
Compute «inv not_rev_example ;; not_rev_example» ("x"↦10) "x". (* ≠10 *)

(* Il problema è che quando si chiama ad esempio It "x" f, la funzione f non dovrebbe avere accesso alla variabile "x" (in effetti con RPP accade così). Fortunatamente è facile determinare se un programma è reversibile o no: basta appunto controllare che quando si usa It x f, If x f, la funzione f non legga/modifichi x. *)

Fixpoint inb (x : string) (l : list string) : bool :=
  match l with
  | [] => false
  | y::l => (x =? y) || (inb x l)
  end.

Fixpoint rev_strict' (f : RPPM) (l : list string) : bool :=
  match f with
  | Id => false
  | Ne x => inb x l
  | Su x => inb x l
  | Pr x => inb x l
  | Co f g => rev_strict' f l || rev_strict' g l
  | It x f => inb x l || rev_strict' f (x::l)
  | If x f g h => inb x l ||
    rev_strict' f (x::l) || rev_strict' g (x::l) || rev_strict' h (x::l)
  end.

Definition rev_strict (f : RPPM) := negb (rev_strict' f []).

Compute rev_strict not_rev_example.
Compute rev_strict (inc "x" "y").

(* In realtà questo è un controllo piuttosto stringente: per avere un programma reversibile è sufficiente che quando si usa It x f, If x f, la funzione f non modifichi x (ma può comunque leggerlo). *)

Fixpoint rev' (f : RPPM) (l : list string) : bool :=
  match f with
  | Id => false
  | Ne x => inb x l
  | Su x => inb x l
  | Pr x => inb x l
  | Co f g => rev' f l || rev' g l
  | It x f => rev' f (x::l)
  | If x f g h => rev' f (x::l) || rev' g (x::l) || rev' h (x::l)
  end.

Definition rev (f : RPPM) := negb (rev' f []).

Compute rev not_rev_example.

(* It' ripete |x| volte inv f se x < 0; è rev ma non rev_strict *)
Definition It' x f := If x (It x f) Id (It x (inv f)).
Compute rev_strict (It' "x" (Su "y")).
Compute rev (It' "x" (Su "y")).

(* Ovviamente se una funzione è rev_strict allora è anche rev. Penso non sia troppo difficile dimostrare l'opposto, ovvero che data una funzione rev è sempre possibile trovarne una equivalente che è rev_strict *)

Theorem rev_to_rev_strict : ∀ f, rev f = true →
  ∃ g, «f» = «g» ∧ rev_strict g = true.
Admitted.

(* La proposizione 1 diventa quindi: *)

Theorem proposition_1_l : ∀ f, rev f = true → «f;;inv f» = «Id».
Admitted.

(* Una nota: ho messo come assioma l'estensionalità delle funzioni, quindi due funzioni che si comportano allo stesso modo possono essere considerate uguali; se no lavorare con state sarebbe scomodo. *)

(* Altra nota: il motivo per cui rappresento la reversibilità con bool anzichè Prop è che data una funzione concreta, usare bool permette di avere un calcolo automatico (tramite rev o rev_strict) mentre con Prop bisognerebbe ogni volta scrivere una dimostrazione. Forse scriverò in futuro una versione Prop: di solito sono più utili appunto nelle dimostrazioni. *)

(* Altri esempi di funzioni RPPM : *)

(* add x y aggiunge y a x *)
Definition add x y := It' y (Su x).
Definition sub x y := inv (add x y).

(* mult x y z aggiunge y*z a x *)
Definition mult x y z := It' z (add x y).
Compute «mult "x" "y" "z"» ("x"↦10; "y"↦15; "z"↦-30) "x".

(* less x y z incrementa x di 1 se y < z *)
Definition less x y z := sub y z;;If y Id Id (Su x);;add y z.
Compute «less "x" "y" "z"» ("x"↦10; "y"↦15; "z"↦16) "x".

Definition cp x y z i := 








