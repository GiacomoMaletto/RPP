import basic

open list

namespace RPP

@[simp] def Id1 := Id 1

@[simp] def call : ℕ → RPP
| 0       := Id1
| (i + 1) := Id i ‖ Sw ;; call i

@[simp] def call_list : list ℕ → RPP
| []       := Id 0
| (i :: l) := call i ;; call_list l

@[simp] def prepare : list ℕ → list ℕ
| []       := []
| (i :: l) := (i + (l.filter (λ j, i < j)).length) :: prepare l

def rewire (l : list ℕ) : RPP := call_list (reverse (prepare l))

-- ⌊ \lf ⌉ \rc
notation `⌊` l:(foldr `, ` (h t, list.cons h t) list.nil `⌉`) := rewire l

def inc := It Su

@[simp] lemma inc_arity : inc.arity = 2 := rfl

lemma inc_def (n : ℕ) (x : ℤ) : ‹inc› [n, x] = [n, x + n] :=
begin
  rw [inc], simp [ev],
  induction n generalizing x, simp, simp [ev, *], ring
end

def dec := inc⁻¹

@[simp] lemma dec_arity : dec.arity = 2 := rfl

lemma dec_def (n : ℕ) (x : ℤ) : ‹dec› [n, x] = [n, x - n] :=
by { rw [dec, proposition_1, inc_def], congr, ring }

def mul := It inc

lemma mul_def (n m : ℕ) (x : ℤ) : ‹mul› [n, m, x] = [n, m, x + n * m] :=
begin
  simp [mul, ev], induction n with n hn,
  simp,
  rw [function.iterate_succ_apply', hn, inc_def],
  simp, ring
end

def Pa1 := Pa
def Pa2 := Pa
infix `‖₁` : 55 := Pa1
infix `‖₂` : 55 := Pa2

def square := Id1 ‖₁ Sw ;; inc ;; mul ;; dec ;; Id1 ‖₁ Sw

lemma square_def (n : ℕ) (x : ℤ) : ‹square› [n, x, 0] = [n, x + n * n, 0] :=
begin
  simp [square, ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw Pa1, simp [ev] },
  rw ev_split, simp, rw inc_def, simp },
  rw mul_def },
  rw ev_split, simp, rw dec_def, simp },
  rw Pa1, simp [ev] }
end

def less := dec ;; Id1 ‖₁ If Su Id1 Id1 ;; inc

@[simp] lemma less_arity : less.arity = 3 := rfl

@[simp] lemma if_gtz (f g h : RPP) (x : ℤ) (l : list ℤ) (H : 0 < x) :
  ‹If f g h› (x :: l) = x :: ‹f› l :=
begin
  cases x, cases x,
  simp at H, contradiction,
  refl,
  simp at H, contradiction
end

@[simp] lemma if_ltz (f g h : RPP) (x : ℤ) (l : list ℤ) (H : x < 0) :
  ‹If f g h› (x :: l) = x :: ‹h› l :=
begin
  cases x, cases x,
  simp at H, contradiction,
  simp at H, linarith,
  refl
end

@[simp] lemma if_gez (f g : RPP) (x : ℤ) (l : list ℤ) (H : 0 ≤ x) :
  ‹If f f g› (x :: l) = x :: ‹f› l :=
begin
  cases x, cases x,
  refl,
  refl,
  simp at H, contradiction
end

lemma less_def (n m : ℕ) : ‹less› [n, m, 0] = [n, m, ite (n < m) 1 0] :=
begin
  simp [less, ev],
  conv in (‹dec› _) { rw ev_split, simp, rw dec_def, simp },
  rw Pa1, simp [ev],
  have h : n < m ∨ n = m ∨ m < n := trichotomous n m,
  rcases h with h | h | h,
  { have H : (0 : ℤ) < m - n, by linarith,
    rw if_gtz, simp [ev, *], rw ev_split, simp [inc_def], assumption },
  { rw h, simp [ev], rw ev_split, simp [inc_def] },
  { have H₁ : ¬ (n < m), by linarith,
    have H₂ : (m - n : ℤ) < 0, by linarith,
    rw if_ltz, simp [ev, *], rw ev_split, simp [inc_def], assumption }
end

end RPP