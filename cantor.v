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
  end%Z.

(* \laq « f » \raq *)
Notation "« f »" := (evaluate f).

Definition weak n f := Id (n - 1) ‖ f.

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

Definition id := Id 1.
Definition inc := It Su.
Definition dec := inv inc.

Definition ifzsw :=
  If inc id id ;; \[3;2;1]\ ;;
  If id Sw id ;; dec ;; \[3;1;2]\.

Definition cu :=
  It (id ‖ Su ;; If id Su id ;; ifzsw ;; Pr) ;; id ‖ Sw.

Definition cp :=
  inc ;; id ‖ (It (Su ;; inc) ;; dec) ;; dec ;;
  \[1;4;2]\ ;; inc ;; \[1;3;2]\.

Definition push := cp ;; \[3;1;2]\ ;; inv cu.
Definition pop := inv push.

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
  | SU i n => S (nth (pred i) l 0)
  | PR i n => nth (pred i) l 0
  | CO F Gs => EVALUATE F (map (λ G, EVALUATE G l) Gs)
  | RE F G => match l with []=>0
    | n::l' => fst (fst (iter
      (λ p, match p with (a,x,y) => (EVALUATE G (a::x::y), S x, y) end)
      n
      (EVALUATE F l', 0, l')))
    end
  end.

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







