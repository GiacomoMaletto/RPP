Require Import Unicode.Utf8 Lia.

Inductive RPP : nat → Type :=
  | Nu : RPP 0
  | Id : RPP 1
  | Ne : RPP 1
  | Su : RPP 1
  | Pr : RPP 1
  | Sw : RPP 2
  | Co {j : nat}   (f g : RPP j)           : RPP j
  | Pa {j k: nat}  (f : RPP j) (g : RPP k) : RPP (j + k)
  | It {j : nat}   (f : RPP j)             : RPP (j + 1)
  | If {j : nat}   (f g h : RPP j)         : RPP (j + 1).

Declare Custom Entry rpp.
Declare Scope rpp_scope.
Notation "<{ e }>" := e
  (at level 0, e custom rpp at level 99) : rpp_scope.
Notation "( x )" := x
  (in custom rpp at level 0, x at level 200) : rpp_scope.
Notation "{ x }" := x
  (in custom rpp at level 0, x constr at level 98) : rpp_scope.
Notation "x" := x
  (in custom rpp at level 0, x constr at level 0) : rpp_scope.
Notation "f x" := (f x)
  (in custom rpp at level 0, only parsing) : rpp_scope.
Notation "f ; g" := (Co f g)
  (in custom rpp at level 70, left associativity).
Notation "f ‖ g" := (Pa f g)
  (in custom rpp at level 70, left associativity).

(* altrimenti dentro rpp questi parametri sono per forza da esplicitare *)
Arguments length {A} _ %rpp_scope.

Open Scope rpp_scope.

Fixpoint inv {j} (f : RPP j) : RPP j :=
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

Create HintDb rpp_hint.
#[export] Hint Unfold inv : rpp_hint.
Arguments inv {j} _ %rpp_scope.

Lemma double_inverse : ∀ [j] (f : RPP j), inv (inv f) = f.
Proof. induction f; try constructor; try simpl; congruence. Qed.

Fixpoint Id' (n : nat) : RPP n :=
  match n as m0 return (RPP m0) with
    | 0%nat => Nu
    | S m0 => <{ Id ‖ Id' m0 }>
  end.

Fixpoint arity {j} (f : RPP j) : nat :=
  match f with
  | Nu => 0
  | Id | Ne | Su | Pr => 1
  | Sw => 2
  | <{ f; g }> => arity f
  | <{ f ‖ g }> => (arity f) + (arity g)
  | It f => S (arity f)
  | If f g h => S (arity f)
  end.

#[export] Hint Unfold arity : rpp_hint.
Arguments arity {j} _ %rpp_scope.

Proposition arity_index : ∀ {j} (f : RPP j),
  arity f = j.
Proof.
  intros. induction f; simpl; lia.
Qed.

Hint Rewrite @arity_index : rpp_hint.