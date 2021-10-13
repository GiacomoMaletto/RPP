import computability.primrec

import library
import sqrt_lemmas

open list

namespace RPP

def mkpairᵢ :=
  less ;;
  ⌊2, 0, 1⌉ ;;
  If (Id₁ ‖ square ;; Sw ;; Id₁ ‖ inc ;; Sw)
     (Id₁ ‖ inc ;; Sw ;; Id₁ ‖ (square ;; inc) ;; Sw)
     Id₁ ;;
  ⌊1, 2, 0⌉ ;;
  less⁻¹

@[simp] lemma mkpairᵢ_arity : mkpairᵢ.arity = 5 := rfl

@[simp] lemma mkpairᵢ_def (n m : ℕ) (l : list ℤ) :
  ‹mkpairᵢ› (n :: m :: 0 :: 0 :: 0 :: l) = n :: m :: 0 :: (nat.mkpair n m) :: 0 :: l :=
begin
  cases em (n < m) with h;
  simp [mkpairᵢ, ev, nat.mkpair, rewire, *], ring
end

def sqrt_step :=
  Su ‖ If Su Id₁ Id₁ ;;
  ⌊2, 0, 1⌉ ;;
  If (Id₁ ‖ Pr) (Su ;; Sw ‖ Su) Id₁ ;;
  Sw ;; If Pr Id₁ Id₁ ;;
  Id₁ ‖ Sw

def sqrt := It sqrt_step

local prefix `√` : 70 := nat.sqrt

@[simp] lemma sqrt_def (n : ℕ) (l : list ℤ) :
  ‹sqrt› (n :: 0 :: 0 :: 0 :: 0 :: l) =
  n :: (n - √n * √n) :: (√n + √n - (n - √n * √n)) :: 0 :: √n :: l :=
begin
  simp [sqrt, ev],
  induction n with n hn,
  simp,
  rw [function.iterate_succ_apply', hn], clear hn,
  cases (sqrt_succ_or n) with h h,

  have H₁ := sqrt_lemma_1 n h,
  have H₂ : (0 : ℤ) < n - √n * √n + 1, by { have h := nat.sqrt_le n, norm_cast, linarith },
  simp[sqrt_step, ev, rewire, *], split, ring, ring,

  have H₁ := sqrt_lemma_2 n h,
  have H₂ : (n : ℤ) = √n + √n + √n * √n, by { symmetry, rw ←sub_eq_zero, rw ←H₁, ring },
  simp[sqrt_step, ev, rewire, *], split, ring, ring
end

def unpairᵢ_fwd :=
  sqrt ;;
  ⌊0, 1, 4, 2, 3⌉ ;;
  Id 2 ‖ dec ;;
  Id 3 ‖ Ne ;;
  Id 3 ‖ If Id₁ Id₁ Pr ;;
  ⌊0, 4, 1, 2, 3⌉

@[simp] lemma unpairᵢ_fwd_arity : unpairᵢ_fwd.arity = 5 := rfl

@[simp] lemma unpairᵢ_fwd_def (n : ℕ) (l : list ℤ) :
  ‹unpairᵢ_fwd› (n :: 0 :: 0 :: 0 :: 0 :: l) =
  n :: (ite (n - √n * √n < √n) (-1) 0) :: (n - √n * √n) :: √n :: (n - √n * √n - √n) :: l :=
begin
  have h : (↑√n - (↑√n + ↑√n - (↑n - ↑√n * ↑√n)) : ℤ) = n - √n * √n - √n, by ring,
  cases em (n - √n * √n < √n) with h₁ h₁,

  have h₂ : (n - √n * √n - √n : ℤ) < 0,
  by { simp, have H := nat.sqrt_le n, norm_cast, assumption },
  simp [unpairᵢ_fwd, ev, rewire, *],

  have h₂ : (0 : ℤ) ≤ n - √n * √n - √n,
  by { simp, have H := nat.sqrt_le n, norm_cast, simp * at * },
  simp [unpairᵢ_fwd, ev, rewire, *]
end

def unpairᵢ :=
  unpairᵢ_fwd ;;
  Id₁ ‖ If Id₁
           (⌊0, 1, 3, 2, 4⌉ ;; Id₁ ‖ inc ‖ inc ;; ⌊0, 1, 3, 2, 4⌉)
           (⌊0, 3, 1, 4, 2⌉ ;; inc ‖ inc ;; ⌊0, 2, 4, 1, 3⌉) ;;
  unpairᵢ_fwd⁻¹

@[simp] lemma unpairᵢ_arity : unpairᵢ.arity = 7 := rfl

@[simp] lemma unpairᵢ_def (n : ℕ) (l : list ℤ) : 
  ‹unpairᵢ› (n :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: l) =
  n :: 0 :: 0 :: 0 :: 0 :: (nat.unpair n).1 :: (nat.unpair n).2 :: l :=
begin
  rw [unpairᵢ, nat.unpair], simp [ev],
  have H := nat.sqrt_le n,
  cases em (n - √n * √n < √n) with h h,
  norm_cast, simp [ev, rewire, *],
  have h₁ : √n ≤ n - √n * √n, by linarith,
  norm_cast, simp [ev, rewire, *]
end

def mkpair := mkpairᵢ ;; ⌊3, 2, 4, 5, 6, 0, 1⌉ ;; unpairᵢ⁻¹

@[simp] lemma mkpair_arity : mkpair.arity = 7 := rfl

@[simp] theorem mkpair_def (n m : ℕ) (l : list ℤ) :
  ‹mkpair› (n :: m :: 0 :: 0 :: 0 :: 0 :: 0 :: l) =
  (nat.mkpair n m) :: 0 :: 0 :: 0 :: 0 :: 0:: 0 :: l :=
by simp [mkpair, ev, rewire]

def unpair := mkpair⁻¹

@[simp] lemma unpair_arity : unpair.arity = 7 := rfl

@[simp] theorem unpair_def (n : ℕ) (l : list ℤ) :
  ‹unpair› (n :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: l) =
  (nat.unpair n).1 :: (nat.unpair n).2 :: 0 :: 0 :: 0 :: 0 :: 0 :: l :=
by simp [unpair]

end RPP