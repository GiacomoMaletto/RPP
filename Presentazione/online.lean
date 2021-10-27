import data.int.basic
import data.list.basic
import logic.function.iterate
import tactic.linarith
import tactic.omega

open list

inductive RPP
| Id (n : ℕ) : RPP
| Ne : RPP
| Su : RPP
| Pr : RPP
| Sw : RPP
| Co (f g : RPP) : RPP
| Pa (f g : RPP) : RPP
| It (f : RPP) : RPP
| If (f g h : RPP) : RPP

namespace RPP

infix `;;` : 50 := Co
infix `‖` : 55 := Pa

attribute [pp_nodot] It
attribute [pp_nodot] If



def t := Sw ;; (Ne ‖ Su)



@[simp] def inv : RPP → RPP
| (Id n)     := Id n
| Ne         := Ne
| Su         := Pr
| Pr         := Su
| Sw         := Sw
| (f ;; g)   := inv g ;; inv f
| (f ‖ g)    := inv f ‖ inv g
| (It f)     := It (inv f)
| (If f g h) := If (inv f) (inv g) (inv h)

notation f `⁻¹` : 60 := inv f


#reduce t⁻¹
#reduce (Su⁻¹)⁻¹


example (f : RPP) : (f⁻¹)⁻¹ = f :=
begin
  induction f
  with n f g hf hg f g hf hg f hf f g h hf hg hh,
  { refl },
  { refl },
  { refl },
  { refl },
  { refl },
  { rw inv, rw inv, rw hf, rw hg },
  { rw inv, rw inv, rw hf, rw hg },
  { rw inv, rw inv, rw hf },
  { rw inv, rw inv, rw hf, rw hg, rw hh }
end

@[simp] lemma inv_involute (f : RPP) : (f⁻¹)⁻¹ = f :=
by induction f; simp*

@[simp] def arity : RPP → ℕ
| (Id n)     := n
| Ne         := 1
| Su         := 1
| Pr         := 1
| Sw         := 2
| (f ;; g)   := max f.arity g.arity
| (f ‖ g)    := f.arity + g.arity
| (It f)     := f.arity + 1
| (If f g h) := max (max f.arity g.arity) h.arity + 1

@[simp] lemma arity_inv (f : RPP) : f⁻¹.arity = f.arity :=
by { induction f; simp [*, max_comm] }

prefix `↓` : 70 := int.to_nat

def ev : RPP → list ℤ → list ℤ
| (Id n)     X                    := X
| Ne         (x :: X)             := -x :: X
| Su         (x :: X)             := (x + 1) :: X
| Pr         (x :: X)             := (x - 1) :: X
| Sw         (x :: y :: X)        := y :: x :: X
| (f ;; g)   X                    := ev g (ev f X)
| (f ‖ g)    X                    := ev f (take f.arity X) ++
                                     ev g (drop f.arity X)
| (It f)     (x :: X)             := x :: ((ev f)^[↓x] X)
| (If f g h) (0 :: X)             := 0 :: ev g X
| (If f g h) (((n : ℕ) + 1) :: X) := (n + 1) :: ev f X
| (If f g h) (-[1+ n] :: X)       := -[1+ n] :: ev h X
| _          X                    := X

notation `‹` f `›` : 50 := ev f



#eval ‹t› [3,0]

example (x y : ℤ) : ‹t› [x, y] = [-y, x+1] :=
by refl



@[simp] lemma ev_nil (f : RPP) : ‹f› [] = [] :=
by { induction f; simp [ev, *] }

@[simp] lemma ev_length (f : RPP) (X : list ℤ) :
  (‹f› X).length = X.length :=
begin
  induction f generalizing X; cases X with x X,
  any_goals {simp [ev, *], done},
  { cases X with x X; refl },
  { simp [ev], rw [f_ih_f, f_ih_g],
    rw [←length_append, take_append_drop], refl },
  { simp [ev], induction (↓x), refl,
    rw [function.iterate_succ_apply'], simp * },
  { cases x, cases x, all_goals {simp [ev, *]} }
end

lemma pa_co_pa (f f' g g' : RPP) (X : list ℤ) :
  f.arity = f'.arity →
  ‹f ‖ g ;; f' ‖ g'› X = ‹(f ;; f') ‖ (g ;; g')› X :=
begin
  intro h,
  simp [ev], rw [←h, max_self], clear h,
  cases (le_total f.arity X.length) with H H,
  { rw [take_append_of_le_length, drop_append_of_le_length],
    rw [take_all_of_le, drop_eq_nil_of_le],
    all_goals {simp *} },
  { rw [take_all_of_le H, drop_eq_nil_of_le H],
    rw [take_all_of_le, drop_eq_nil_of_le],
    all_goals {simp *} }
end

theorem inv_co_l (f : RPP) (X : list ℤ) :
  ‹f ;; f⁻¹› X = X :=
begin
  induction f generalizing X; cases X with x X,
  any_goals {simp [ev, *], done},
  { cases X with y X, refl, simp [ev] },
  { simp [ev, *] at * },
  { rw [inv, pa_co_pa], simp [ev, *] at *, rw arity_inv },
  { simp [ev] at *, apply function.left_inverse.iterate f_ih },
  { rcases x with ⟨n, n⟩; simp [ev, *] at * }
end

lemma inv_co_r (f : RPP) (X : list ℤ) :
  ‹f⁻¹ ;; f› X = X :=
by { convert inv_co_l (f⁻¹) X, rw inv_involute }

@[simp] theorem inv_iff (f : RPP) (X Y : list ℤ) :
  ‹f⁻¹› X = Y ↔ ‹f› Y = X :=
begin
  split; intro h; rw ←h,
  conv_rhs {rw ←inv_co_r f X}, refl,
  conv_rhs {rw ←inv_co_l f Y}, refl,
end

end RPP

open RPP













