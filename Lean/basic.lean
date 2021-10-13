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
infix `‖` : 55 := Pa -- ‖ \Vert

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

notation f `⁻¹` : 60 := inv f -- ⁻¹ \-1

@[simp] lemma inv_involute (f : RPP) : (f⁻¹)⁻¹ = f :=
by { induction f; simp * }

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
| (Id n)     l                    := l
| Ne         (x :: l)             := -x :: l
| Su         (x :: l)             := (x + 1) :: l
| Pr         (x :: l)             := (x - 1) :: l
| Sw         (x :: y :: l)        := y :: x :: l
| (f ;; g)   l                    := ev g (ev f l)
| (f ‖ g)    l                    := ev f (take f.arity l) ++ ev g (drop f.arity l)
| (It f)     (x :: l)             := x :: ((ev f)^[↓x] l)
| (If f g h) (0 :: l)             := 0 :: ev g l
| (If f g h) (((n : ℕ) + 1) :: l) := (n + 1) :: ev f l
| (If f g h) (-[1+ n] :: l)       := -[1+ n] :: ev h l
| _          l                    := l

notation `‹` f `›` : 50 := ev f -- ‹ \f › \fr

@[simp] lemma ev_nil (f : RPP) : ‹f› [] = [] :=
by { induction f; simp [ev, *] }

@[simp] lemma ev_length (f : RPP) (l : list ℤ) : (‹f› l).length = l.length :=
begin
  induction f generalizing l; cases l with x l,
  any_goals {simp [ev, *], done},
  { cases l with x l; refl },
  { simp [ev], rw [f_ih_f, f_ih_g, ←length_append, take_append_drop], refl },
  { simp [ev], induction (↓x), refl, rw [function.iterate_succ_apply'], simp * },
  { cases x, cases x, all_goals {simp [ev, *]} }
end

lemma pa_co_pa (f f' g g' : RPP) (l : list ℤ) : f.arity = f'.arity →
  ‹f ‖ g ;; f' ‖ g'› l = ‹(f ;; f') ‖ (g ;; g')› l :=
begin
  intro h,
  simp [ev], rw [←h, max_self], clear h,
  cases (le_total f.arity l.length) with H H,
  { rw [take_append_of_le_length, drop_append_of_le_length],
    rw [take_all_of_le, drop_eq_nil_of_le],
    refl, all_goals {simp *} },
  { rw [take_all_of_le H, drop_eq_nil_of_le H, ev_nil, append_nil],
    rw [take_all_of_le, drop_eq_nil_of_le, ev_nil, append_nil],
    all_goals {simp *} }
end

theorem inv_co_l (f : RPP) (l : list ℤ) : ‹f ;; f⁻¹› l = l :=
begin
  induction f generalizing l; cases l with x l,
  any_goals {simp [ev, *], done},
  { cases l with y l, refl, simp [ev] },
  { simp [ev, *] at * },
  { rw [inv, pa_co_pa], simp [ev, *] at *, rw arity_inv },
  { simp [ev] at *, apply function.left_inverse.iterate f_ih },
  { rcases x with ⟨n, n⟩; simp [ev, *] at * }
end

lemma inv_co_r (f : RPP) (l : list ℤ) : ‹f⁻¹ ;; f› l = l :=
by { convert inv_co_l (f⁻¹) l, rw inv_involute }

@[simp] theorem inv_iff (f : RPP) (l m : list ℤ) : ‹f⁻¹› l = m ↔ ‹f› m = l :=
begin
  split; intro h; rw ←h,
  conv_rhs {rw ←inv_co_r f l}, refl,
  conv_rhs {rw ←inv_co_l f m}, refl,
end

lemma take_ev (f : RPP) (n : ℕ) (l : list ℤ) : f.arity ≤ n →
  take n (‹f› l) = ‹f› (take n l) :=
begin
  intro h,
  induction f generalizing n l,
  any_goals { cases l; cases n; refl },
  { rw arity at h, rcases n with _ | _ | n, linarith, linarith,
    rcases l with _ | ⟨x, _ | l⟩; refl },
  { rw [arity, max_le_iff] at h, cases h with h₁ h₂, simp [ev, *] },
  case Pa : f g hf hg
  { rw arity at h,
    have h₁ : f.arity ≤ n := by linarith,
    have h₂ : g.arity ≤ n := by linarith,
    simp only [ev],
    rw [take_append_eq_append_take, hf _ _ h₁],
    rw [take_take, min_eq_right h₁],
    rw [take_take, min_eq_left h₁],
    rw [ev_length, length_take],
    cases (le_total f.arity l.length) with H H,
    rw [min_eq_left H, hg, ←drop_take], congr, omega, omega,
    rw [drop_eq_nil_of_le H, drop_eq_nil_of_le, take_all_of_le]; simp * },
  case It : f hf
  { cases l with x l; cases n; try {refl},
    simp [ev],
    induction (↓x) generalizing l, refl,
    replace h := nat.succ_le_succ_iff.mp h,
    simp [arity, *] at * },
  { cases l with x l; cases n; try {refl},
    rw arity at h, replace h := nat.succ_le_succ_iff.mp h, simp [max_le_iff] at h, 
    rcases h with ⟨⟨h₁, h₂⟩, h₃⟩,
    cases x, cases x, all_goals {simp [ev, *]} }
end

lemma drop_ev (f : RPP) (n : ℕ) (l : list ℤ) : f.arity ≤ n →
  drop n (‹f› l) = drop n l :=
begin
  intro h,
  induction f generalizing n l,
  { refl },
  any_goals { rw arity at h, cases n, linarith, cases l; refl },
  { rw arity at h, rcases n with _ | _ | n, linarith, linarith,
    rcases l with _ | ⟨x, _ | l⟩; refl },
  { rw [arity, max_le_iff] at h, cases h with h₁ h₂, simp [ev, *] },
  case Pa : f g hf hg
  { rw arity at h,
    have h₁ : f.arity ≤ n := by linarith,
    have h₂ : g.arity ≤ n := by linarith,
    simp only [ev],
    rw [drop_append_eq_append_drop, hf _ _ h₁],
    rw [drop_eq_nil_of_le, nil_append],
    rw [ev_length, length_take ],
    cases (le_total f.arity l.length) with H H,
    rw [min_eq_left H, hg, drop_drop], congr, omega, omega,
    rw [drop_eq_nil_of_le H, ev_nil, drop_nil, drop_eq_nil_of_le], linarith, simp * },
  case It : f hf
  { cases n, rw arity at h, linarith, cases l with x l, refl,
    rw [ev, drop],
    induction (↓x) generalizing l, refl,
    replace h := nat.succ_le_succ_iff.mp h, simp [arity, *] at * },
  { cases n, rw arity at h, linarith, cases l with x l, refl,
    rw arity at h, replace h := nat.succ_le_succ_iff.mp h, simp [max_le_iff] at h, 
    rcases h with ⟨⟨h₁, h₂⟩, h₃⟩,
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