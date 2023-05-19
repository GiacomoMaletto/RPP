import data.int.basic
import data.list.basic
import logic.function.iterate
import tactic.linarith
import tactic.omega

open list

inductive rpp
| Id (n : ℕ) : rpp
| Ne : rpp
| Su : rpp
| Pr : rpp
| Sw : rpp
| Co (f g : rpp) : rpp
| Pa (f g : rpp) : rpp
| It (f : rpp) : rpp
| If (f g h : rpp) : rpp

namespace rpp

infix `;;` : 50 := Co
infix `‖` : 55 := Pa -- ‖ \Vert

attribute [pp_nodot] It
attribute [pp_nodot] If

@[simp] def inv : rpp → rpp
| (Id n)     := Id n
| Ne         := Ne
| Su         := Pr
| Pr         := Su
| Sw         := Sw
| (f ;; g)   := inv g ;; inv f
| (f ‖ g)    := inv f ‖ inv g
| (It f)     := It (inv f)
| (If f g h) := If (inv f) (inv g) (inv h)

notation (name := inv) f `⁻¹` : 60 := inv f -- ⁻¹ \-1

@[simp] lemma inv_involute (f : rpp) : (f⁻¹)⁻¹ = f :=
by { induction f; simp * }

@[simp] def arity : rpp → ℕ
| (Id n)     := n
| Ne         := 1
| Su         := 1
| Pr         := 1
| Sw         := 2
| (f ;; g)   := max f.arity g.arity
| (f ‖ g)    := f.arity + g.arity
| (It f)     := f.arity + 1
| (If f g h) := max (max f.arity g.arity) h.arity + 1

@[simp] lemma arity_inv (f : rpp) : f⁻¹.arity = f.arity :=
by { induction f; simp [*, max_comm] }

prefix `↓` : 70 := int.to_nat

def ev : rpp → list ℤ → list ℤ
| (Id n)     X                    := X
| Ne         (x :: X)             := -x :: X
| Su         (x :: X)             := (x + 1) :: X
| Pr         (x :: X)             := (x - 1) :: X
| Sw         (x :: y :: X)        := y :: x :: X
| (f ;; g)   X                    := ev g (ev f X)
| (f ‖ g)    X                    := ev f (take f.arity X) ++ ev g (drop f.arity X)
| (It f)     (x :: X)             := x :: ((ev f)^[↓x] X)
| (If f g h) (0 :: X)             := 0 :: ev g X
| (If f g h) (((n : ℕ) + 1) :: X) := (n + 1) :: ev f X
| (If f g h) (-[1+ n] :: X)       := -[1+ n] :: ev h X
| _          X                    := X

notation (name := ev) `‹` f `›` : 50 := ev f -- ‹ \f › \fr

@[simp] lemma ev_nil (f : rpp) : ‹f› [] = [] :=
by { induction f; simp [ev, *] }

@[simp] lemma ev_length (f : rpp) (X : list ℤ) : (‹f› X).length = X.length :=
begin
  induction f generalizing X; cases X with x X,
  any_goals {simp [ev, *], done},
  { cases X with x X; refl },
  { simp [ev], rw [f_ih_f, f_ih_g, ←length_append, take_append_drop], refl },
  { simp [ev], induction (↓x), refl, rw [function.iterate_succ_apply'], simp * },
  { cases x, cases x, all_goals {simp [ev, *]} }
end

lemma pa_co_pa (f f' g g' : rpp) (X : list ℤ) : f.arity = f'.arity →
  ‹f ‖ g ;; f' ‖ g'› X = ‹(f ;; f') ‖ (g ;; g')› X :=
begin
  intro h,
  simp [ev], rw [←h, max_self], clear h,
  cases (le_total f.arity X.length) with H H,
  { rw [take_append_of_le_length, drop_append_of_le_length],
    rw [take_all_of_le, drop_eq_nil_of_le],
    refl, all_goals {simp *} },
  { rw [take_all_of_le H, drop_eq_nil_of_le H, ev_nil, append_nil],
    rw [take_all_of_le, drop_eq_nil_of_le, ev_nil, append_nil],
    all_goals {simp *} }
end

theorem inv_co_l (f : rpp) (X : list ℤ) : ‹f ;; f⁻¹› X = X :=
begin
  induction f generalizing X; cases X with x X,
  any_goals {simp [ev, *], done},
  { cases X with y X, refl, simp [ev] },
  { simp [ev, *] at * },
  { rw [inv, pa_co_pa], simp [ev, *] at *, rw arity_inv },
  { simp [ev] at *, apply function.left_inverse.iterate f_ih },
  { rcases x with ⟨n, n⟩; simp [ev, *] at * }
end

lemma inv_co_r (f : rpp) (X : list ℤ) : ‹f⁻¹ ;; f› X = X :=
by { convert inv_co_l (f⁻¹) X, rw inv_involute }

@[simp] theorem inv_iff (f : rpp) (X Y : list ℤ) : ‹f⁻¹› X = Y ↔ ‹f› Y = X :=
begin
  split; intro h; rw ←h,
  conv_rhs {rw ←inv_co_r f X}, refl,
  conv_rhs {rw ←inv_co_l f Y}, refl,
end

lemma take_ev (f : rpp) (n : ℕ) (X : list ℤ) : f.arity ≤ n →
  take n (‹f› X) = ‹f› (take n X) :=
begin
  intro h,
  induction f generalizing n X,
  any_goals { cases X; cases n; refl },
  { rw arity at h, rcases n with _ | _ | n, linarith, linarith,
    rcases X with _ | ⟨x, _ | l⟩; refl },
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
    cases (le_total f.arity X.length) with H H,
    rw [min_eq_left H, hg, ←drop_take], congr, omega, omega,
    rw [drop_eq_nil_of_le H, drop_eq_nil_of_le, take_all_of_le]; simp * },
  case It : f hf
  { cases X with x X; cases n; try {refl},
    simp [ev],
    induction (↓x) generalizing X, refl,
    replace h := nat.succ_le_succ_iff.mp h,
    simp [arity, *] at * },
  { cases X with x X; cases n; try {refl},
    rw arity at h, replace h := nat.succ_le_succ_iff.mp h, simp [max_le_iff] at h, 
    rcases h with ⟨⟨h₁, h₂⟩, h₃⟩,
    cases x, cases x, all_goals {simp [ev, *]} }
end

lemma drop_ev (f : rpp) (n : ℕ) (X : list ℤ) : f.arity ≤ n →
  drop n (‹f› X) = drop n X :=
begin
  intro h,
  induction f generalizing n X,
  { refl },
  any_goals { rw arity at h, cases n, linarith, cases X; refl },
  { rw arity at h, rcases n with _ | _ | n, linarith, linarith,
    rcases X with _ | ⟨x, _ | l⟩; refl },
  { rw [arity, max_le_iff] at h, cases h with h₁ h₂, simp [ev, *] },
  case Pa : f g hf hg
  { rw arity at h,
    have h₁ : f.arity ≤ n := by linarith,
    have h₂ : g.arity ≤ n := by linarith,
    simp only [ev],
    rw [drop_append_eq_append_drop, hf _ _ h₁],
    rw [drop_eq_nil_of_le, nil_append],
    rw [ev_length, length_take ],
    cases (le_total f.arity X.length) with H H,
    rw [min_eq_left H, hg, drop_drop], congr, omega, omega,
    rw [drop_eq_nil_of_le H, ev_nil, drop_nil, drop_eq_nil_of_le], linarith, simp * },
  case It : f hf
  { cases n, rw arity at h, linarith, cases X with x X, refl,
    rw [ev, drop],
    induction (↓x) generalizing X, refl,
    replace h := nat.succ_le_succ_iff.mp h, simp [arity, *] at * },
  { cases n, rw arity at h, simp at h, contradiction, cases X with x X, refl,
    rw arity at h, replace h := nat.succ_le_succ_iff.mp h, simp [max_le_iff] at h, 
    rcases h with ⟨⟨h₁, h₂⟩, h₃⟩,
    cases x, cases x, all_goals {simp [ev, *]} }
end

theorem ev_split (f : rpp) (X : list ℤ) :
  ‹f› X = ‹f› (take f.arity X) ++ drop f.arity X :=
begin
  rw [←take_ev, ←drop_ev, take_append_drop], refl, refl 
end

lemma ev_split_le (f : rpp) (X : list ℤ) (n : ℕ) : f.arity ≤ n →
  ‹f› X = ‹f› (take n X) ++ drop n X :=
begin
  intro h, rw [←take_ev, ←drop_ev, take_append_drop], assumption, assumption
end

end rpp