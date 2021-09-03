import data.int.basic
import data.list.basic
import logic.function.iterate
import tactic.linarith
import tactic.omega

import list_lemmas

open list

inductive RPP
| Id (n : ℕ)
| Ne
| Su
| Pr
| Sw
| Co (f g : RPP)
| Pa (f g : RPP)
| It (f : RPP)
| If (f g h : RPP)

namespace RPP

infix `;;` : 50 := Co
infix `‖` : 55 := Pa

attribute [pp_nodot] It
attribute [pp_nodot] If

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

lemma inv_involute (f : RPP) : (f⁻¹)⁻¹ = f :=
by { induction f; simp [inv, *] }

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

lemma arity_inv (f : RPP) : f⁻¹.arity = f.arity :=
by { induction f; simp [*, max_comm] }

prefix `↓` : 70 := int.to_nat

def ev : RPP → list ℤ → list ℤ
| (Id n)      l                    := l
| Ne          (x :: l)             := -x :: l
| Su          (x :: l)             := (x + 1) :: l
| Pr          (x :: l)             := (x - 1) :: l
| Sw          (x :: y :: l)        := y :: x :: l
| (f ;; g)    l                    := ev g (ev f l)
| (f ‖ g)     l                    := ev f (take f.arity l) ++ ev g (drop f.arity l)
| (It f)      (x :: l)             := x :: ((ev f)^[↓x] l)
| (If f g h)  (0 :: l)             := 0 :: ev g l
| (If f g h)  (((n : ℕ) + 1) :: l) := (n + 1) :: ev f l
| (If f g h)  (-[1+ n] :: l)       := -[1+ n] :: ev h l
| _           l                    := l

notation `‹` f `›` : 50 := ev f

@[simp] lemma ev_nil (f : RPP) : ‹f› [] = [] :=
by { induction f; simp [ev, *] }

@[simp] lemma ev_length (f : RPP) (l : list ℤ) : (‹f› l).length = l.length :=
begin
  induction f generalizing l; cases l with x l; try {rw ev_nil}; try {simp [ev, *], done},
  { cases l with x l; refl },
  { simp [ev], rw [f_ih_f, f_ih_g, ←length_append, take_append_drop], refl },
  { simp [ev], induction (↓x), refl, rw [function.iterate_succ_apply'], simp * },
  { cases x, cases x, all_goals {simp [ev, *]} }
end

lemma pa_co_pa (f g f' g' : RPP) (l : list ℤ) : f.arity = g.arity →
  ‹g ‖ g'› (‹f ‖ f'› l) = ‹(f ;; g) ‖ (f' ;; g')› l :=
begin
  intro h,
  simp [ev], rw [←h, max_self],
  cases (le_total f.arity l.length) with H H,
  { rw [take_append_of_le_length, drop_append_of_le_length],
    rw [take_all_of_le, drop_eq_nil_of_le],
    refl, any_goals {simp}, any_goals {assumption} },
  { rw [take_all_of_le H, drop_eq_nil_of_le H, ev_nil, append_nil],
    rw [take_all_of_le, drop_eq_nil_of_le, ev_nil, append_nil],
    any_goals {simpa} }
end

lemma proposition_2 (f g f' g' : RPP) (l : list ℤ) : f.arity = g.arity →
  ‹f ‖ f' ;; g ‖ g'› l = ‹(f ;; g) ‖ (f' ;; g')› l :=
begin
  intro h,
  calc ‹f ‖ f' ;; g ‖ g'› l = ‹g ‖ g'› (‹f ‖ f'› l) : rfl
                        ... = ‹(f ;; g) ‖ (f' ;; g')› l : by rwa ←pa_co_pa
end

lemma co_if (f g h f' g' h' : RPP) (l : list ℤ) :
  ‹If f g h ;; If f' g' h'› l = ‹If (f ;; f') (g ;; g') (h ;; h')› l :=
begin
  cases l with x l, refl,
  cases x, cases x, all_goals {simp [ev, *]}
end

lemma proposition_1_co_l (f : RPP) (l : list ℤ) : ‹f ;; f⁻¹› l = l :=
begin
  induction f generalizing l; cases l with x l; try {rw ev_nil}; try {simp [ev, *], done},
  { cases l with x l, refl, cases l with y l, refl, simp [ev] },
  { simp [ev, *] at * },
  { simp, rw proposition_2, simp [ev, *] at *, rw ←arity_inv },
  { simp [ev] at *, apply function.left_inverse.iterate f_ih },
  { simp, rw co_if, cases x, cases x, all_goals {simp [ev, *]} }
end

lemma proposition_1_co_r (f : RPP) (l : list ℤ) : ‹f⁻¹ ;; f› l = l :=
by { convert proposition_1_co_l (f⁻¹) l, rw inv_involute }

theorem proposition_1 (f : RPP) (l m : list ℤ) : ‹f⁻¹› l = m ↔ ‹f› m = l :=
begin
  split; intro h; rw ←h,
  conv_rhs {rw ←proposition_1_co_r f l}, refl,
  conv_rhs {rw ←proposition_1_co_l f m}, refl,
end

lemma take_ev (f : RPP) (n : ℕ) (l : list ℤ) : f.arity ≤ n →
  take n (‹f› l) = ‹f› (take n l) :=
begin
  intro h,
  induction f generalizing n l; try { cases l; cases n; trivial },
  { cases l with x l; cases n with n; try {trivial},
    cases l; cases n; try {trivial},
    simp at h, linarith },
  { simp at h, cases h with h₁ h₂, simp [ev, *] },
  case Pa : f g hf hg
  { simp at h, 
    have h₁ : f.arity ≤ n := by linarith,
    have h₂ : g.arity ≤ n := by linarith,
    simp [ev, *],
    rw [take_append_sub, hf _ _ h₁],
    rw [take_take, min_eq_right h₁],
    rw [take_take, min_eq_left h₁],
    congr, simp,
    cases (le_total f.arity l.length) with H H,
    rw [min_eq_left H, hg, ←drop_take], congr, omega, omega,
    rw [drop_eq_nil_of_le H, drop_eq_nil_of_le], simp, rwa take_all_of_le, linarith },
  { cases l with x l; cases n; try {trivial}, simp [ev],
    induction (↓x) generalizing l, refl,
    simp at *, rw [ih, f_ih], apply nat.succ_le_succ_iff.mp h },
  { cases l with x l; cases n; try {trivial},
    simp at h, replace h := nat.succ_le_succ_iff.mp h,
    replace h := max_le_iff.mp h, cases h with h₁ h₃,
    replace h₁ := max_le_iff.mp h₁, cases h₁ with h₁ h₂,
    cases x, cases x, all_goals {simp [ev, *]} }
end

lemma drop_ev (f : RPP) (n : ℕ) (l : list ℤ) : f.arity ≤ n →
  drop n (‹f› l) = drop n l :=
begin
  intro h,
  induction f generalizing n l,
  { refl },
  any_goals { cases l with x l, simp,
              cases n, simp at h, contradiction, refl },
  { cases l with x l, simp,
    cases l with y l, simp [ev],
    cases n, simp at h, contradiction,
    cases n, simp at h, linarith, refl },
  { simp at h, cases h with h₁ h₂, simp [ev, *] },
  case Pa : f g hf hg
  { simp at h, 
    have h₁ : f.arity ≤ n := by linarith,
    have h₂ : g.arity ≤ n := by linarith,
    simp [ev, *],
    rw [drop_append_sub, hf _ _ h₁],
    rw [drop_eq_nil_of_le], simp,
    cases (le_total f.arity l.length) with H H,
    rw [min_eq_left H, hg, drop_drop], congr, omega, omega,
    rw drop_eq_nil_of_le H, simp, rw drop_eq_nil_of_le, linarith,
    simp, left, exact h₁ },
  { cases l with x l; cases n; simp [ev] at *, contradiction,
    induction (↓x) generalizing l, refl,
    simp at *, rw [ih, f_ih], apply nat.succ_le_succ_iff.mp h},
  { cases l with x l; cases n; simp [ev] at *, contradiction,
    replace h := nat.succ_le_succ_iff.mp h,
    replace h := max_le_iff.mp h, cases h with h₁ h₃,
    replace h₁ := max_le_iff.mp h₁, cases h₁ with h₁ h₂,
    cases x, cases x, all_goals {simp [ev, *]} }
end

theorem ev_split (f : RPP) (l : list ℤ) :
  ‹f› l = ‹f› (take f.arity l) ++ drop f.arity l :=
begin
  rw [←take_ev, ←drop_ev, take_append_drop], refl, refl 
end

lemma ev_split_le (f : RPP) (l : list ℤ) (n : ℕ) : f.arity ≤ n →
  ‹f› l = ‹f› (take n l) ++ drop n l :=
begin
  intro h, rw [←take_ev, ←drop_ev, take_append_drop], assumption, assumption
end

end RPP