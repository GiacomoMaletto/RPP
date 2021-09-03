import pair

def nat.prec_loop (F G : ℕ → ℕ) (z n : ℕ) :=
  nat.elim (F z) (λ (y IH : ℕ), G (nat.mkpair z (nat.mkpair y IH))) n

open list

namespace RPP
namespace convert

def thesis (F : ℕ → ℕ) (f : RPP) :=
  ∀ (z : ℤ) (n : ℕ), ‹f› (z :: n :: repeat 0 (f.arity-2)) = (z + F n) :: n :: repeat 0 (f.arity-2)

lemma thesis_le (F : ℕ → ℕ) (f : RPP) : thesis F f → ∀ (a : ℕ), f.arity-2 ≤ a →
  ∀ (z : ℤ) (n : ℕ), ‹f› (z :: n :: repeat 0 a) = (z + F n) :: n :: repeat 0 a :=
begin
  rw thesis, intros H a h z n,
  cases (le_total f.arity 2) with h₁,

  have h₂ : f.arity-2 = 0, from sub_eq_zero_iff_le.mpr h₁,
  rw h₂ at H, simp at *, rw ev_split_le _ _ 2 h₁, simp, rw H, refl,

  rw [←nat.add_sub_of_le h, repeat_add],
  rw [←cons_append, ←cons_append],
  rw ev_split,
  rw [take_append_of_le_length, drop_append_of_le_length],
  rw [take_all_of_le, drop_eq_nil_of_le],
  simp,
  rw H, refl,
  all_goals { simp, omega }
end

def succ := Su ;; Sw ;; inc ;; Sw

@[simp] lemma succ_arity : succ.arity = 2 := rfl

lemma succ_def (z : ℤ) (n : ℕ) : ‹succ› [z, n] = [(z + n.succ), n] :=
begin
  rw succ, simp [ev], rw inc_def, simp [ev], ring
end

def left := Id1 ‖₁ unpair' ;; ⌊6, 0⌉ ;; inc ;; (Id1 ‖₁ unpair' ;; ⌊6, 0⌉)⁻¹

lemma left_def (z : ℤ) (n : ℕ) :
  ‹left› (z :: n :: repeat 0 6) = (z + (nat.unpair n).fst) :: n :: repeat 0 6 :=
begin
  rw left, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw Pa1, simp [ev], rw unpair'_def},
  rw rewire, simp [ev] },
  rw ev_split, simp [inc_def] },
  rw rewire, simp [ev] }},
  rw Pa1, simp [ev], rw proposition_1, rw unpair'_def
end

def right := Id1 ‖₁ unpair' ;; ⌊7, 0⌉ ;; inc ;; (Id1 ‖₁ unpair' ;; ⌊7, 0⌉)⁻¹

lemma right_def (z : ℤ) (n : ℕ) :
  ‹right› (z :: n :: repeat 0 6) = (z + (nat.unpair n).snd) :: n :: repeat 0 6 :=
begin
  rw right, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw Pa1, simp [ev], rw unpair'_def},
  rw rewire, simp [ev] },
  rw ev_split, simp [inc_def] },
  rw rewire, simp [ev] }},
  rw Pa1, simp [ev], rw proposition_1, rw unpair'_def
end

def pair_fwd (f g : RPP) :=
  Id 1 ‖₁ (Sw ;; f) ;;
  Id 2 ‖₁ (Sw ;; g) ;;
  ⌊0, 3, 1, 2⌉ ;;
  Id 2 ‖₁ mkpair' ;;
  ⌊5, 0⌉

lemma pair_fwd_arity_le1 (f g : RPP) : 7 ≤ (pair_fwd f g).arity :=
begin
  rw [pair_fwd, Pa1], simp
end

lemma pair_fwd_arity_le2 (f g : RPP) : f.arity + 1 ≤ (pair_fwd f g).arity :=
begin
  rw pair_fwd, rw Pa1, simp, left, left, left, left,
  rw [add_comm, add_le_add_iff_left],
  apply le_max_right
end

lemma pair_fwd_arity_le3 (f g : RPP) : g.arity + 2 ≤ (pair_fwd f g).arity :=
begin
  rw pair_fwd, rw Pa1, simp, left, left, left, right,
  rw [add_comm, add_le_add_iff_left],
  apply le_max_right
end

lemma pair_fwd_arity (f g : RPP) : ∃ a,
  (pair_fwd f g).arity = a + 7 ∧ f.arity-2 ≤ a + 4 ∧ g.arity-2 ≤ a + 3 :=
begin
  have h₁ := pair_fwd_arity_le1 f g,
  have h₂ := pair_fwd_arity_le2 f g,
  have h₃ := pair_fwd_arity_le3 f g,
  use (pair_fwd f g).arity - 7,
  split, omega,
  split, omega, omega
end

lemma pair_fwd_def (F G : ℕ → ℕ) (f g : RPP) : thesis F f → thesis G g → ∀ (z : ℤ) (n : ℕ),
  ‹pair_fwd f g› (z :: n :: repeat 0 ((pair_fwd f g).arity-2)) =
  nat.mkpair (F n) (G n) :: z :: n :: F n :: G n :: 0 :: repeat 0 ((pair_fwd f g).arity-6) :=
begin
  intros hF hG z n,
  have HF := thesis_le _ _ hF, clear hF,
  have HG := thesis_le _ _ hG, clear hG,
  rcases pair_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁,
  rw pair_fwd, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw Pa1, simp [ev],
  rw [←repeat_succ, ←repeat_succ, ←repeat_succ, ←repeat_succ], ring_nf,
  rw HF _ h₂, simp },
  rw Pa1, simp [ev],
  rw [←repeat_succ, ←repeat_succ, ←repeat_succ], ring_nf,
  rw HG _ h₃, simp },
  rw rewire, simp [ev] },
  rw Pa1, simp [ev], rw ev_split, simp [mkpair'_def] },
  rw rewire, simp [ev] }
end

def pair (f g : RPP) := pair_fwd f g ;; inc ;; (pair_fwd f g)⁻¹

lemma pair_arity_eq (f g : RPP) : (pair f g).arity = (pair_fwd f g).arity :=
begin
  rw pair, simp [rewire, arity_inv],
  have h := pair_fwd_arity_le1 f g, linarith
end

lemma pair_def (F G : ℕ → ℕ) (f g : RPP) : thesis F f → thesis G g → ∀ (z : ℤ) (n : ℕ),
  ‹pair f g› (z :: n :: repeat 0 ((pair f g).arity-2)) =
  (z + nat.mkpair (F n) (G n)) :: n :: repeat 0 ((pair f g).arity-2) :=
begin
  intros hF hG z n, rw pair_arity_eq,
  unfold pair, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  rw pair_fwd_def _ _ _ _ hF hG },
  rw ev_split, simp [inc_def] }},
  rw proposition_1, rw pair_fwd_def _ _ _ _ hF hG
end

def comp_fwd (f g : RPP) :=
  Id 1 ‖₁ (Sw ;; g ;; Sw) ;;
  Id 2 ‖₁ (Sw ;; f) ;;
  ⌊2, 0⌉

lemma comp_fwd_arity_le1 (f g : RPP) : 4 ≤ (comp_fwd f g).arity :=
begin
  rw [comp_fwd, Pa1], simp, left, right,
  rw [show 4 = 2 + 2, by refl], rw add_le_add_iff_left, apply le_max_left
end

lemma comp_fwd_arity_le2 (f g : RPP) : f.arity + 2 ≤ (comp_fwd f g).arity :=
begin
  rw comp_fwd, rw Pa1, simp, left, right,
  rw [add_comm, add_le_add_iff_left],
  apply le_max_right
end

lemma comp_fwd_arity_le3 (f g : RPP) : g.arity + 1 ≤ (comp_fwd f g).arity :=
begin
  rw comp_fwd, rw Pa1, simp, left, left,
  rw [add_comm, add_le_add_iff_left],
  apply le_max_right
end

lemma comp_fwd_arity (f g : RPP) : ∃ a,
  (comp_fwd f g).arity = a + 4 ∧ f.arity-2 ≤ a ∧ g.arity-2 ≤ a + 1 :=
begin
  have h₁ := comp_fwd_arity_le1 f g,
  have h₂ := comp_fwd_arity_le2 f g,
  have h₃ := comp_fwd_arity_le3 f g,
  use (comp_fwd f g).arity - 4,
  split, omega,
  split, omega, omega
end

lemma comp_fwd_def (F G : ℕ → ℕ) (f g : RPP) : thesis F f → thesis G g → ∀ (z : ℤ) (n : ℕ),
  ‹comp_fwd f g› (z :: n :: repeat 0 ((comp_fwd f g).arity-2)) =
  F (G n) :: z :: n :: ↑(G n) :: repeat 0 ((comp_fwd f g).arity-4) :=
begin
  intros hF hG z n,
  have HF := thesis_le _ _ hF, clear hF,
  have HG := thesis_le _ _ hG, clear hG,
  rcases comp_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁,
  rw comp_fwd, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  rw Pa1, simp [ev], rw [←repeat_succ], rw HG _ h₃, simp [ev] },
  rw Pa1, simp [ev], rw HF _ h₂, simp },
  rw rewire, simp [ev] }
end

def comp (f g : RPP) := comp_fwd f g ;; inc ;; (comp_fwd f g)⁻¹

lemma comp_arity_eq (f g : RPP) : (comp f g).arity = (comp_fwd f g).arity :=
begin
  rw comp, simp [rewire, arity_inv],
  have h := comp_fwd_arity_le1 f g, linarith
end

lemma comp_def (F G : ℕ → ℕ) (f g : RPP) : thesis F f → thesis G g → ∀ (z : ℤ) (n : ℕ),
  ‹comp f g› (z :: n :: repeat 0 ((comp f g).arity-2)) =
  (z + F (G n)) :: n :: repeat 0 ((comp f g).arity-2) :=
begin
  intros hF hG z n, rw comp_arity_eq,
  unfold comp, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  rw comp_fwd_def _ _ _ _ hF hG },
  rw ev_split, simp [inc_def] }},
  rw proposition_1, rw comp_fwd_def _ _ _ _ hF hG
end

def prec_loop (g : RPP) :=
  Id 2 ‖₁ mkpair ;;
  Id 1 ‖₁ mkpair ;;
  Id 1 ‖₁ (Sw ;; g) ;;
  Id 2 ‖₁ unpair ;;
  Id 3 ‖₁ unpair ;;
  ⌊2, 3, 1, 0, 4⌉ ;;
  Id 1 ‖₁ Su ‖₁ Id 1 ‖₁ mkpair ;;
  ⌊3, 0, 1, 2⌉

def prec_fwd (f g : RPP) :=
  Id 1 ‖₁ unpair ;;
  ⌊0, 2, 3, 1⌉ ;;
  Id 2 ‖₁ f ;;
  ⌊0, 1, 4, 3, 5, 2⌉ ;;
  Id 1 ‖₁ It (prec_loop g) ;;
  ⌊5, 0⌉

lemma prec_fwd_arity_le1 (f g : RPP) : 12 ≤ (prec_fwd f g).arity :=
begin
  rw [prec_fwd, prec_loop, Pa1], simp,
  left, right, rw [show 12 = 1 + (10 + 1), by refl], simp
end

lemma prec_fwd_arity_le2 (f g : RPP) : f.arity + 2 ≤ (prec_fwd f g).arity :=
begin
  rw [prec_fwd, prec_loop, Pa1], simp,
  left, left, left, right, rw add_comm
end

lemma prec_fwd_arity_le3 (f g : RPP) : g.arity + 3 ≤ (prec_fwd f g).arity :=
begin
  rw [prec_fwd, prec_loop, Pa1], simp,
  left, right, rw [show g.arity + 3 = 1 + (g.arity + 1 + 1), by ring], simp,
  left, left, left, right,
  rw [add_comm, add_le_add_iff_left],
  apply le_max_right
end

lemma prec_fwd_arity (f g : RPP) : ∃ a,
  (prec_fwd f g).arity = a + 12 ∧ f.arity-2 ≤ a+8 ∧ g.arity-2 ≤ a+7 :=
begin
  have h₁ := prec_fwd_arity_le1 f g,
  have h₂ := prec_fwd_arity_le2 f g,
  have h₃ := prec_fwd_arity_le3 f g,
  use (prec_fwd f g).arity - 12,
  split, omega,
  split, omega, omega
end

lemma prec_loop_def (F G : ℕ → ℕ) (f g : RPP) : thesis G g → ∀ (Z N s : ℕ), ∃ (s' : ℕ),
  ‹prec_loop g› (s :: Z :: N :: nat.prec_loop F G Z N :: repeat 0 ((prec_fwd f g).arity-6)) =
  s' :: Z :: (N + 1) :: nat.prec_loop F G Z (N + 1) :: repeat 0 ((prec_fwd f g).arity-6) :=
begin
  intros hG Z N s, use nat.mkpair s (nat.prec_loop F G Z N),
  have HG := thesis_le _ _ hG, clear hG,
  rcases prec_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁,
  rw prec_loop, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw Pa1, simp [ev], rw ev_split, simp [mkpair_def] },
  rw Pa1, simp [ev], rw ev_split, simp [mkpair_def] },
  rw Pa1, simp [ev],
  rw [←repeat_succ, ←repeat_succ, ←repeat_succ, ←repeat_succ,
      ←repeat_succ, ←repeat_succ, ←repeat_succ], ring_nf,
  rw HG _ h₃, simp [ev] },
  rw Pa1, simp [ev], rw ev_split, simp [unpair_def] },
  rw Pa1, simp [ev], rw ev_split, simp [unpair_def] },
  rw rewire, simp [ev] },
  rw Pa1, simp [ev], rw ev_split, simp [mkpair_def] },
  rw rewire, simp [ev] },
  rw [nat.prec_loop, nat.prec_loop, nat.elim], simp
end

lemma it_prec_loop_def (F G : ℕ → ℕ) (f g : RPP) : thesis G g → ∀ (Z N : ℕ), ∃ (s : ℕ),
  ‹prec_loop g›^[N] (0 :: Z :: 0 :: F Z :: repeat 0 ((prec_fwd f g).arity-6)) =
  s :: Z :: N :: nat.prec_loop F G Z N :: repeat 0 ((prec_fwd f g).arity-6) :=
begin
  intros hG Z N, induction N with N hN,
  use 0, simp [ev], refl,
  rcases hN with ⟨s, hN⟩,
  have h := prec_loop_def F G f g hG Z N s, rcases h with ⟨s', h⟩,
  use s', rw [function.iterate_succ_apply', hN, h], refl
end

lemma prec_fwd_def (F G : ℕ → ℕ) (f g : RPP) :
  thesis F f → thesis G g → ∀ (n : ℕ), ∃ (s : ℕ), ∀ (z : ℤ),
  ‹prec_fwd f g› (z :: n :: repeat 0 ((prec_fwd f g).arity-2)) =
  nat.prec_loop F G (nat.unpair n).fst (nat.unpair n).snd ::
    z :: (nat.unpair n).snd :: s :: (nat.unpair n).fst :: (nat.unpair n).snd ::
    repeat 0 ((prec_fwd f g).arity-6) :=
begin
  intros hF hG n,
  have HF := thesis_le _ _ hF, clear hF,
  have h := it_prec_loop_def F G f g hG (nat.unpair n).fst (nat.unpair n).snd,
  rcases h with ⟨s, h⟩, use s, intro z,
  rcases prec_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁ at *,
  rw [show a + 12 - 6 = a + 6, by refl] at h,
  rw prec_fwd, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  conv { congr, skip,
  rw Pa1, simp [ev], rw ev_split, simp [unpair_def] },
  rw rewire, simp [ev] },
  rw Pa1, simp [ev],
  rw [←repeat_succ, ←repeat_succ, ←repeat_succ, ←repeat_succ,
      ←repeat_succ, ←repeat_succ, ←repeat_succ, ←repeat_succ], ring_nf,
  rw HF _ h₂, simp [ev] },
  rw rewire, simp [ev] },
  rw Pa1, simp [ev],
  rw [←repeat_succ, ←repeat_succ, ←repeat_succ,
      ←repeat_succ, ←repeat_succ, ←repeat_succ], ring_nf,
  rw h },
  rw rewire, simp [ev] }
end

def prec (f g : RPP) := prec_fwd f g ;; inc ;; (prec_fwd f g)⁻¹

lemma prec_arity_eq (f g : RPP) : (prec f g).arity = (prec_fwd f g).arity :=
begin
  rw prec, simp [rewire, arity_inv],
  have h := prec_fwd_arity_le1 f g, linarith
end

lemma prec_def (F G : ℕ → ℕ) (f g : RPP) : thesis F f → thesis G g → ∀ (z : ℤ) (n : ℕ),
  ‹prec f g› (z :: n :: repeat 0 ((prec f g).arity-2)) =
  (z + nat.prec_loop F G (nat.unpair n).fst (nat.unpair n).snd) ::
    n :: repeat 0 ((prec f g).arity-2) :=
begin
  intros hF hG z n, rw prec_arity_eq,
  have h := prec_fwd_def _ _ _ _ hF hG n, rcases h with ⟨s, h⟩,
  unfold prec, simp [ev],
  conv { to_lhs,
  conv { congr, skip,
  conv { congr, skip,
  rw h },
  rw ev_split, simp [inc_def] }},
  rw proposition_1, rw h
end

theorem proposition_5 (F : ℕ → ℕ) : nat.primrec F → ∃ f, thesis F f :=
begin
  intro h, induction h,
  case zero : { use Id 0, simp [thesis, ev] },
  case succ : { use succ, exact succ_def },
  case left : { use left, exact left_def },
  case right : { use right, exact right_def },
  case pair : G₁ G₂ h₁ h₂ ih₁ ih₂
  { rcases ih₁ with ⟨g₁, ih₁⟩, rcases ih₂ with ⟨g₂, ih₂⟩,
    use pair g₁ g₂, rw thesis, exact pair_def _ _ _ _ ih₁ ih₂ },
  case comp : G₁ G₂ h₁ h₂ ih₁ ih₂
  { rcases ih₁ with ⟨g₁, ih₁⟩, rcases ih₂ with ⟨g₂, ih₂⟩,
    use comp g₁ g₂, rw thesis, exact comp_def _ _ _ _ ih₁ ih₂ },
  case prec : G₁ G₂ h₁ h₂ ih₁ ih₂
  { rcases ih₁ with ⟨g₁, ih₁⟩, rcases ih₂ with ⟨g₂, ih₂⟩,
    use prec g₁ g₂, rw thesis, exact prec_def _ _ _ _ ih₁ ih₂ }
end

end convert
end RPP