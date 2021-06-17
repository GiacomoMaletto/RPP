Require Import Unicode.Utf8 List ZArith.
Import ListNotations.
Set Implicit Arguments.

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

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

Open Scope Z_scope.

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

Open Scope nat_scope.

Definition id := Id 1.

Definition weak n f := Id (n - 1) ‖ f.
Definition cast n f :=
  match arity f <=? n with
  | true => f ‖ Id (n - arity f)
  | false => Id n
  end.
Definition wc i n f := cast n (weak i f).

Definition ita f := It f ;; Ne ;; It f ;; Ne.
Definition itr f := It f ;; Ne ;; inv (It f) ;; Ne.

Definition inc := It Su.
Definition dec := inv inc.
Definition add := itr Su.
Definition sub := inv add.
Definition less := sub ;; id ‖ If Su id id ;; add.

Fixpoint call i :=
  match i with
  | O => Id 0
  | 1 => Id 0
  | 2 => Sw
  | S j => weak j Sw ;; call j
  end.
Fixpoint call_list l :=
  match l with
  | [] => Id 0
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

Definition ifzsw := If inc id id ;; \[3;2;1]\ ;;
  If id Sw id ;; dec ;; \[3;1;2]\.

Definition cu :=
  It (id ‖ Su ;; If id Su id ;; ifzsw ;; Pr) ;; id ‖ Sw.

Definition cp :=
  inc ;; id ‖ (It (Su ;; inc) ;; dec) ;; dec ;;
  \[1;4;2]\ ;; inc ;; \[1;3;2]\.

Definition push := cp ;; \[3;1;2]\ ;; inv cu.

Definition pop := inv push.

Open Scope Z_scope.

Compute «add» [-5;2;3;4].
Compute «less» [-5;2;3;4].
Compute «\[4;2;6;1]%nat\» [1;2;3;4;5;6;7;8].
Compute «ifzsw» [0;2;0].
Compute «ifzsw» [1;2;0].
Compute «cu» [83;0;0;0].
Compute «cp» [5;7;0;0].
Compute «push» [5;7;0;0].
Compute «pop» [83;0;0;0].

Open Scope nat_scope.

Inductive PRF :=
  | ZE : nat → PRF
  | SU : nat → nat → PRF
  | PR : nat → nat → PRF
  | CO : PRF → list PRF → PRF
  | RE : PRF → PRF → PRF.

Fixpoint ARITY (F : PRF) : nat :=
  match F with
  | ZE n | SU _ n | PR _ n => n
  | CO F Gs => list_max (map ARITY Gs)
  | RE F G => max (S (ARITY F)) (pred (ARITY G))
  end.

Fixpoint EVALUATE F (l : list nat) : nat :=
  match F with
  | ZE n => O
  | SU i n => S (nth (pred i) l O)
  | PR i n => (nth (pred i) l O)
  | CO F Gs => EVALUATE F (map (λ G, EVALUATE G l) Gs)
  | RE F G => match l with []=>0
    | n::l' => fst (fst (iter
      (λ p, match p with (a,x,y) => (EVALUATE G (a::x::y), S x, y) end)
      n
      (EVALUATE F l', 0, l')))
    end
  end.

Definition ADD := RE (PR 1 1) (CO (SU 1 1) [PR 1 3]).
Definition PRE := RE (ZE 0) (PR 2 3).
Definition SUB := RE (PR 1 1) (CO PRE [PR 1 3]).
Definition MUL := RE (ZE 1) (CO ADD [PR 1 3;PR 3 3]).
Compute EVALUATE ADD [4;4].
Compute EVALUATE PRE [4].
Compute EVALUATE SUB [3;5].
Compute EVALUATE MUL [44;313].

Fixpoint co_loading n m gs :=
  match gs with
  | [] => Id 0
  | g::gs' => Id n ‖ (\[m]\ ;; g) ;; co_loading (S n) m gs'
  end.

Fixpoint convert (F : PRF) : RPP :=
  match F with
  | ZE n => Id n
  | SU i n => Su ;; \[1+i;1]\ ;; inc ;; inv(\[1+i;1]\) ‖ Id (n - i)
  | PR i n => \[1+i;1]\ ;; inc ;; inv(\[1+i;1]\) ‖ Id (n - i)
  | CO F Gs => let (n, m) := (ARITY (CO F Gs), length Gs) in
    co_loading 1 (1+n) (map convert Gs) ;;
    \seq (2+m) n\ ;;
    Id n ‖ (convert F) ;;
    inv (co_loading 1 (1+n) (map convert Gs) ;;
    \seq (2+m) n\)
  | RE F G => let n := pred (ARITY (RE F G)) in
    Id 2 ‖ \seq (1+n) 6\ ;;
    Id 7 ‖ convert F ;;
    Id 6 ‖ Sw ;;
    Id 1 ‖ It (Id 3 ‖ (convert G ;; Sw) ;; \[1;4]\ ;; push ;; Id 5 ‖ Su) ;;
    \[7;1]\ ;;
    inc ;;
    inv (Id 2 ‖ \seq (1+n) 6\ ;;
    Id 7 ‖ convert F ;;
    Id 6 ‖ Sw ;;
    Id 1 ‖ It (Id 3 ‖ (convert G ;; Sw) ;; \[1;4]\ ;; push ;; Id 5 ‖ Su) ;;
    \[7;1]\)
  end.

Definition pad f l := evaluate f (l ++ repeat 0%Z (arity f - length l)).

Compute pad (convert PRE) [0;5]%Z.
Compute pad (convert ADD) [0;3;4]%Z.
Compute pad (convert SUB) [0;2;5]%Z.
Compute pad (convert MUL) [0;2;2]%Z.

Fixpoint count f : nat :=
  match f with
  | Id _ | Ne | Su | Pr | Sw => 1
  | Co f g => count f + count g
  | Pa f g => count f + count g
  | It f => 1 + count f
  | If f g h => 1 + count f + count g + count h
  end.

Compute count (convert ADD).







