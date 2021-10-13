import basic

open list

namespace RPP

@[simp] def Id₁ := Id 1

@[simp] def call : ℕ → RPP
| 0       := Id₁
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

@[simp] lemma inc_def (n : ℕ) (x : ℤ) (l : list ℤ) : ‹inc› (n :: x :: l) = n :: (x + n) :: l :=
begin
  rw [inc], simp [ev],
  induction n generalizing x, simp, simp [ev, *], ring
end

def dec := inc⁻¹

@[simp] lemma dec_arity : dec.arity = 2 := rfl

@[simp] lemma dec_def (n : ℕ) (x : ℤ) (l : list ℤ) : ‹dec› (n :: x :: l) = n :: (x - n) :: l :=
by simp[dec]

def mul := It inc

@[simp] lemma mul_def (n m : ℕ) (x : ℤ) (l : list ℤ) :
  ‹mul› (n :: m :: x :: l) = n :: m :: (x + n * m) :: l :=
begin 
  simp [mul, ev], induction n with n hn,
  simp,
  simp [function.iterate_succ_apply', *], ring
end

def square := Id₁ ‖ Sw ;; inc ;; mul ;; dec ;; Id₁ ‖ Sw

@[simp] lemma square_def (n : ℕ) (x : ℤ) (l : list ℤ) :
  ‹square› (n :: x :: 0 :: l) = n :: (x + n * n) :: 0 :: l :=
by simp [square, ev]

def less := dec ;; Id₁ ‖ If Su Id₁ Id₁ ;; inc

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

@[simp] lemma less_def (n m : ℕ) (l : list ℤ) :
  ‹less› (n :: m :: 0 :: l) = n :: m :: (ite (n < m) 1 0) :: l :=
begin
  have h : (m : ℤ) - n < 0 ∨ (m : ℤ) - n = 0 ∨ (0 : ℤ) < m - n := trichotomous ((m : ℤ) - n) 0,
  rcases h with h | h | h,
  have H : ¬ (n < m) := by linarith, simp [less, ev, *],
  have H : n = m     := by linarith, simp [less, ev, *],
  have H : n < m     := by linarith, simp [less, ev, *]
end

end RPP