import data.nat.sqrt
import tactic.linarith
import tactic.omega

local prefix `√` : 70 := nat.sqrt

lemma sqrt_succ_or (n : ℕ) : √n.succ = √n ∨ √n.succ = (√n).succ :=
begin
  cases (lt_or_eq_of_le (nat.sqrt_succ_le_succ_sqrt n)) with h₁,
  left, suffices h₂ : √n ≤ √n.succ, from nat.eq_of_le_of_lt_succ h₂ h₁,
  apply nat.sqrt_le_sqrt, exact nat.le_succ n,
  right, exact h
end

lemma sqrt_lemma_1 (n : ℕ) (h : √n.succ = √n) : (0 : ℤ) < √n + √n - (n - √n * √n) :=
begin
  have H : √n = √(n + 1), by omega, clear h,
  apply gt.lt,
  calc ( ↑(√n + √n) - (↑n - ↑(√n * √n)) : ℤ)
      = √n + √n - n + √n * √n : by { norm_cast, ring }
  ... = √(n+1) + √(n+1) - n + √(n+1) * √(n+1) : by rw H
  ... = (√(n+1) + 1) * (√(n+1) + 1) - (n + 1) : by { norm_cast, simp, ring }
  ... ≥ 1 : by { rw ge_iff_le, apply le_sub_iff_add_le.mpr, norm_cast, rw add_comm,
                 exact nat.succ_le_succ_sqrt (n + 1), apply_instance }
end

lemma sqrt_lemma_2 (n : ℕ) (h : √n.succ = (√n).succ) : (√n + √n - (n - √n * √n) : ℤ) = 0 :=
begin
  suffices H₁ : (√n + √n - (n - √n * √n) : ℤ) ≤ 0,
  have H₂ := nat.sqrt_le_add n, linarith,
  have H : √n = √(n+1) - 1, by omega, clear h,
  calc (√n + √n - (n - √n * √n) : ℤ)
      = √n + √n - n + √n * √n : by ring
  ... = ↑(√(n+1)-1) + ↑(√(n+1)-1) - n + ↑(√(n+1)-1) * ↑(√(n+1)-1) : by rw H
  ... = √n + √n - 2 - n + √(n+1) * √(n+1) + 1 - √n - √n : by { rw int.coe_nat_sub, simp, ring,
                                                               apply nat.succ_le_iff.mpr,
                                                               apply nat.sqrt_pos.mpr,
                                                               exact nat.succ_pos n }
  ... = √(n+1) * √(n+1) - (n+1) : by ring
  ... ≤ 0 : by { rw sub_nonpos, norm_cast, exact nat.sqrt_le (n + 1) }
end