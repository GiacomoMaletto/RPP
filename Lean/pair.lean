import computability.primrec

import library
import sqrt_lemmas

open list

namespace RPP

def mkpair' :=
  less ;;
  ⌊2, 0, 1⌉ ;;
  If (Id1 ‖ square ;; Sw ;; Id1 ‖₁ inc ;; Sw)
     (Id1 ‖ inc ;; Sw ;; Id1 ‖₁ (square ;; inc) ;; Sw)
     Id1 ;;
  ⌊1, 2, 0⌉ ;;
  less⁻¹

@[simp] lemma mkpair'_arity : mkpair'.arity = 5 := rfl

lemma mkpair'_def (n m : ℕ) :
  ‹mkpair'› [n, m, 0, 0, 0] = [n, m, 0, nat.mkpair n m, 0] :=
begin
  simp [mkpair', ev, nat.mkpair],
  cases em (n < m) with h,
  
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw ev_split, simp, simp [less_def, *] },
  rw rewire, simp [ev] },
  simp [ev],
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw square_def, simp },
  simp [ev] },
  rw Pa1, simp [ev], rw ev_split, simp [inc_def] },
  simp [ev] }},
  rw rewire, simp [ev] }},
  rw [proposition_1, ev_split], simp, simp [less_def, *],

  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw ev_split, simp, simp [less_def, *] },
  rw rewire, simp [ev] },
  simp [ev],
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw ev_split, simp [inc_def] }},
  simp [ev] },
  rw Pa1, simp [ev], rw square_def, rw ev_split, simp [inc_def] },
  simp [ev] }},
  rw rewire, simp [ev] }},
  rw [proposition_1, ev_split], simp, simp [less_def, *], ring
end

def sqrt_step :=
  Su ‖ If Su Id1 Id1 ;;
  ⌊2, 0, 1⌉ ;;
  If (Id1 ‖ Pr) (Su ;; Sw ‖ Su) Id1 ;;
  Sw ;; If Pr Id1 Id1 ;;
  Id1 ‖₁ Sw

def sqrt := It sqrt_step

local prefix `√` : 70 := nat.sqrt

lemma sqrt_def (n : ℕ) :
  ‹sqrt› [n, 0, 0, 0, 0] = [n, n - √n * √n, √n + √n - (n - √n * √n), 0, √n] :=
begin
  simp [sqrt, ev],
  induction n with n hn,
  simp,
  rw [function.iterate_succ_apply', hn], clear hn,
  simp [sqrt_step, ev],
  cases (sqrt_succ_or n) with h h,

  have H₁ := sqrt_lemma_1 n h,
  have H₂ : (0 : ℤ) < n - √n * √n + 1, by { have h := nat.sqrt_le n, norm_cast, linarith },
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  simp [ev, *] }},
  rw rewire, simp [ev] },
  simp [ev] },
  simp [ev] },
  simp [ev, *] },
  rw Pa1, simp [ev] },
  simp *, split, ring, ring,

  have H₁ := sqrt_lemma_2 n h,
  have H₂ : (n : ℤ) = √n + √n + √n * √n, by { symmetry, rw ←sub_eq_zero, rw ←H₁, ring },
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw H₁, simp [ev] }},
  rw rewire, simp [ev] },
  simp [ev] },
  simp [ev] },
  simp [ev] },
  rw Pa1, simp [ev] },
  simp *, split, ring, ring  
end

def unpair'_fwd :=
  sqrt ;;
  ⌊0, 1, 4, 2, 3⌉ ;;
  Id 2 ‖₁ dec ;;
  Id 3 ‖₁ Ne ;;
  Id 3 ‖₁ If Id1 Id1 Pr ;;
  ⌊0, 4, 1, 2, 3⌉

@[simp] lemma unpair'_fwd_arity : unpair'_fwd.arity = 5 := rfl

lemma unpair'_fwd_def (n : ℕ) :
  ‹unpair'_fwd› [n, 0, 0, 0, 0] =
  [n, ite (n - √n * √n < √n) (-1) 0, n - √n * √n, √n, n - √n * √n - √n] :=
begin
  have h : (↑√n - (↑√n + ↑√n - (↑n - ↑√n * ↑√n)) : ℤ) = n - √n * √n - √n, by ring,
  cases em (n - √n * √n < √n) with h₁ h₁,

  have h₂ : (n - √n * √n - √n : ℤ) < 0,
  by { simp, have H := nat.sqrt_le n, norm_cast, assumption },
  simp [unpair'_fwd, ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw sqrt_def },
  rw rewire, simp [ev] },
  rw Pa1, simp [ev], rw ev_split, simp [dec_def] },
  rw Pa1, simp [ev] },
  rw Pa1, simp [ev, *] },
  rw rewire, simp [ev] },
  simp *,

  have h₂ : (0 : ℤ) ≤ n - √n * √n - √n,
  by { simp, have H := nat.sqrt_le n, norm_cast, simp * at * },
  simp [unpair'_fwd, ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw sqrt_def },
  rw rewire, simp [ev] },
  rw Pa1, simp [ev], rw ev_split, simp [dec_def] },
  rw Pa1, simp [ev] },
  rw Pa1, simp [ev, *] },
  rw rewire, simp [ev] },
  simp *
end

def unpair' :=
  unpair'_fwd ;;
  Id1 ‖₁ If Id1
           (⌊0, 1, 3, 2, 4⌉ ;; Id1 ‖₂ inc ‖₂ inc ;; ⌊0, 1, 3, 2, 4⌉)
           (⌊0, 3, 1, 4, 2⌉ ;; inc ‖₂ inc ;; ⌊0, 2, 4, 1, 3⌉) ;;
  unpair'_fwd⁻¹

@[simp] lemma unpair'_arity : unpair'.arity = 7 := rfl

lemma unpair'_def (n : ℕ) : 
  ‹unpair'› [n, 0, 0, 0, 0, 0, 0] =
  [n, 0, 0, 0, 0, (nat.unpair n).1, (nat.unpair n).2] :=
begin
  rw [unpair', nat.unpair], simp [ev],
  have H := nat.sqrt_le n,
  cases em (n - √n * √n < √n) with h h,

  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  rw ev_split, simp [unpair'_fwd_def] },
  rw Pa1, simp [ev, *],
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw rewire, simp [ev] },
  rw Pa2, norm_cast, simp [ev, inc_def], rw ev_split, simp [inc_def] },
  rw rewire, simp [ev] }}}},
  rw proposition_1, simp *, rw ev_split, simp [unpair'_fwd_def],
  split, intro h₁, linarith, norm_cast,

  have h₁ : √n ≤ n - √n * √n, by linarith,
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  rw ev_split, simp [unpair'_fwd_def] },
  rw Pa1, simp [ev, *],
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw rewire, simp [ev] },
  rw Pa2, norm_cast, simp [ev, inc_def] },
  rw rewire, simp [ev] }}}},
  rw proposition_1, simp *, rw ev_split, simp [unpair'_fwd_def],
  split, intro h₂, linarith, split, norm_cast, norm_cast
end

def mkpair := mkpair' ;; ⌊3, 2, 4, 5, 6, 0, 1⌉ ;; unpair'⁻¹

@[simp] lemma mkpair_arity : mkpair.arity = 7 := rfl

theorem mkpair_def (n m : ℕ) :
  ‹mkpair› [n, m, 0, 0, 0, 0, 0] = [nat.mkpair n m, 0, 0, 0, 0, 0, 0] :=
begin
  rw mkpair, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  rw ev_split, simp [mkpair'_def] },
  rw rewire, simp [ev] }},
  rw [proposition_1, unpair'_def], simp
end

def unpair := mkpair⁻¹

@[simp] lemma unpair_arity : unpair.arity = 7 := rfl

theorem unpair_def (n : ℕ) :
  ‹unpair› [n, 0, 0, 0, 0, 0, 0] =
  [(nat.unpair n).1, (nat.unpair n).2, 0, 0, 0, 0, 0] :=
begin
  rw [unpair, proposition_1, mkpair_def], simp
end

end RPP