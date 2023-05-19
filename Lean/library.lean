import basic

open list

namespace rpp

@[simp] def Id₁ := Id 1

@[simp] def call : ℕ → rpp
| 0       := Id₁
| (i + 1) := Id i ‖ Sw ;; call i

@[simp] def call_list : list ℕ → rpp
| []       := Id 0
| (i :: X) := call i ;; call_list X

@[simp] def prepare : list ℕ → list ℕ
| []       := []
| (i :: X) := (i + (X.filter (λ j, i < j)).length) :: prepare X

def rewire (X : list ℕ) : rpp := call_list (reverse (prepare X))

-- ⌊ \lfl ⌉ \rc
notation `⌊` X:(foldr `, ` (h t, list.cons h t) list.nil `⌉`) := rewire X

def inc := It Su

@[simp] lemma inc_arity : inc.arity = 2 := rfl

@[simp] lemma inc_def (n : ℕ) (x : ℤ) (X : list ℤ) : ‹inc› (n :: x :: X) = n :: (x + n) :: X :=
begin
  rw [inc], simp [ev],
  induction n generalizing x, simp, simp [ev, *], ring
end

def dec := inc⁻¹

@[simp] lemma dec_arity : dec.arity = 2 := rfl

@[simp] lemma dec_def (n : ℕ) (x : ℤ) (X : list ℤ) : ‹dec› (n :: x :: X) = n :: (x - n) :: X :=
by simp[dec]

def mul := It inc

@[simp] lemma mul_def (n m : ℕ) (x : ℤ) (X : list ℤ) :
  ‹mul› (n :: m :: x :: X) = n :: m :: (x + n * m) :: X :=
begin 
  simp [mul, ev], induction n with n hn,
  simp,
  simp [function.iterate_succ_apply', *], ring
end

def square := Id₁ ‖ Sw ;; inc ;; mul ;; dec ;; Id₁ ‖ Sw

@[simp] lemma square_def (n : ℕ) (x : ℤ) (X : list ℤ) :
  ‹square› (n :: x :: 0 :: X) = n :: (x + n * n) :: 0 :: X :=
by simp [square, ev]

def less := dec ;; Id₁ ‖ If Su Id₁ Id₁ ;; inc

@[simp] lemma less_arity : less.arity = 3 := rfl

@[simp] lemma if_gtz (f g h : rpp) (x : ℤ) (X : list ℤ) (H : 0 < x) :
  ‹If f g h› (x :: X) = x :: ‹f› X :=
begin
  cases x, cases x,
  simp at H, contradiction,
  refl,
  simp at H, contradiction
end

@[simp] lemma if_ltz (f g h : rpp) (x : ℤ) (X : list ℤ) (H : x < 0) :
  ‹If f g h› (x :: X) = x :: ‹h› X :=
begin
  cases x, cases x,
  simp at H, contradiction,
  simp at H, linarith,
  refl
end

@[simp] lemma if_gez (f g : rpp) (x : ℤ) (X : list ℤ) (H : 0 ≤ x) :
  ‹If f f g› (x :: X) = x :: ‹f› X :=
begin
  cases x, cases x,
  refl,
  refl,
  simp at H, contradiction
end

@[simp] lemma less_def (n m : ℕ) (X : list ℤ) :
  ‹less› (n :: m :: 0 :: X) = n :: m :: (ite (n < m) 1 0) :: X :=
begin
  have h : (m : ℤ) - n < 0 ∨ (m : ℤ) - n = 0 ∨ (0 : ℤ) < m - n := trichotomous ((m : ℤ) - n) 0,
  rcases h with h | h | h,
  have H : ¬ (n < m) := by linarith, simp [less, ev, *],
  have H : n = m     := by linarith, simp [less, ev, *],
  have H : n < m     := by linarith, simp [less, ev, *]
end

end rpp