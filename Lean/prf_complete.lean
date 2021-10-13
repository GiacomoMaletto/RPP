import pair

def nat.prec_loop (F G : ℕ → ℕ) (z n : ℕ) :=
  nat.elim (F z) (λ (y IH : ℕ), G (nat.mkpair z (nat.mkpair y IH))) n

open list

namespace RPP

def ex_rpp (F : ℕ → ℕ) (f : RPP) :=
  ∀ (z : ℤ) (n : ℕ), ‹f› (z :: n :: repeat 0 (f.arity-2)) = (z + F n) :: n :: repeat 0 (f.arity-2)

lemma ex_rpp_le (F : ℕ → ℕ) (f : RPP) : ex_rpp F f → ∀ (a : ℕ), f.arity-2 ≤ a →
  ∀ (z : ℤ) (n : ℕ), ‹f› (z :: n :: repeat 0 a) = (z + F n) :: n :: repeat 0 a :=
begin
  rw ex_rpp, intros H a h z n,
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

lemma succ_def (z : ℤ) (n : ℕ) : ‹succ› [z, n] = [z + n.succ, n] :=
by { simp [succ, ev], ring }

def left := Id₁ ‖ unpairᵢ ;; ⌊6, 0⌉ ;; inc ;; (Id₁ ‖ unpairᵢ ;; ⌊6, 0⌉)⁻¹

lemma left_def (z : ℤ) (n : ℕ) :
  ‹left› (z :: n :: repeat 0 6) = (z + (nat.unpair n).fst) :: n :: repeat 0 6 :=
by simp [left, ev, rewire]

def right := Id₁ ‖ unpairᵢ ;; ⌊7, 0⌉ ;; inc ;; (Id₁ ‖ unpairᵢ ;; ⌊7, 0⌉)⁻¹

lemma right_def (z : ℤ) (n : ℕ) :
  ‹right› (z :: n :: repeat 0 6) = (z + (nat.unpair n).snd) :: n :: repeat 0 6 :=
by simp [right, ev, rewire]

def pair_fwd (f g : RPP) :=
  Id 1 ‖ (Sw ;; f) ;;
  Id 2 ‖ (Sw ;; g) ;;
  ⌊0, 3, 1, 2⌉ ;;
  Id 2 ‖ mkpairᵢ ;;
  ⌊5, 0⌉

lemma pair_fwd_arity_le1 (f g : RPP) : 7 ≤ (pair_fwd f g).arity :=
by simp [pair_fwd]

lemma pair_fwd_arity_le2 (f g : RPP) : f.arity + 1 ≤ (pair_fwd f g).arity :=
begin
  rw pair_fwd, simp, left, left, left, left,
  rw [add_comm, add_le_add_iff_left],
  apply le_max_right
end

lemma pair_fwd_arity_le3 (f g : RPP) : g.arity + 2 ≤ (pair_fwd f g).arity :=
begin
  rw pair_fwd, simp, left, left, left, right,
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

lemma pair_fwd_def (F G : ℕ → ℕ) (f g : RPP) :
  ex_rpp F f → ex_rpp G g → ∀ (z : ℤ) (n : ℕ),
  ‹pair_fwd f g› (z :: n :: repeat 0 ((pair_fwd f g).arity-2)) =
  nat.mkpair (F n) (G n) :: z :: n :: F n :: G n :: 0 :: repeat 0 ((pair_fwd f g).arity-6) :=
begin
  intros hF hG z n,
  rcases pair_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁,
  have HF := ex_rpp_le _ _ hF _ h₂, clear hF,
  have HG := ex_rpp_le _ _ hG _ h₃, clear hG,
  simp [pair_fwd, ev, rewire, *] at *
end

def pair (f g : RPP) := pair_fwd f g ;; inc ;; (pair_fwd f g)⁻¹

lemma pair_arity_eq (f g : RPP) : (pair f g).arity = (pair_fwd f g).arity :=
begin
  rw pair, simp [rewire, arity_inv],
  have h := pair_fwd_arity_le1 f g, linarith
end

lemma pair_def (F G : ℕ → ℕ) (f g : RPP) : ex_rpp F f → ex_rpp G g → ∀ (z : ℤ) (n : ℕ),
  ‹pair f g› (z :: n :: repeat 0 ((pair f g).arity-2)) =
  (z + nat.mkpair (F n) (G n)) :: n :: repeat 0 ((pair f g).arity-2) :=
begin
  intros hF hG z n, rw pair_arity_eq,
  have H := pair_fwd_def _ _ _ _ hF hG,
  simp [pair, ev, *]
end

def comp_fwd (f g : RPP) :=
  Id 1 ‖ (Sw ;; g ;; Sw) ;;
  Id 2 ‖ (Sw ;; f) ;;
  ⌊2, 0⌉

lemma comp_fwd_arity_le1 (f g : RPP) : 4 ≤ (comp_fwd f g).arity :=
begin
  rw comp_fwd, simp, left, right,
  rw [show 4 = 2 + 2, by refl], rw add_le_add_iff_left, apply le_max_left
end

lemma comp_fwd_arity_le2 (f g : RPP) : f.arity + 2 ≤ (comp_fwd f g).arity :=
begin
  rw comp_fwd, simp, left, right,
  rw [add_comm, add_le_add_iff_left],
  apply le_max_right
end

lemma comp_fwd_arity_le3 (f g : RPP) : g.arity + 1 ≤ (comp_fwd f g).arity :=
begin
  rw comp_fwd, simp, left, left,
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

lemma comp_fwd_def (F G : ℕ → ℕ) (f g : RPP) : ex_rpp F f → ex_rpp G g → ∀ (z : ℤ) (n : ℕ),
  ‹comp_fwd f g› (z :: n :: repeat 0 ((comp_fwd f g).arity-2)) =
  F (G n) :: z :: n :: ↑(G n) :: repeat 0 ((comp_fwd f g).arity-4) :=
begin
  intros hF hG z n,
  rcases comp_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁,
  have HF := ex_rpp_le _ _ hF _ h₂, clear hF,
  have HG := ex_rpp_le _ _ hG _ h₃, clear hG,
  simp [comp_fwd, ev, rewire, *] at *
end

def comp (f g : RPP) := comp_fwd f g ;; inc ;; (comp_fwd f g)⁻¹

lemma comp_arity_eq (f g : RPP) : (comp f g).arity = (comp_fwd f g).arity :=
begin
  rw comp, simp [rewire, arity_inv],
  have h := comp_fwd_arity_le1 f g, linarith
end

lemma comp_def (F G : ℕ → ℕ) (f g : RPP) : ex_rpp F f → ex_rpp G g → ∀ (z : ℤ) (n : ℕ),
  ‹comp f g› (z :: n :: repeat 0 ((comp f g).arity-2)) =
  (z + F (G n)) :: n :: repeat 0 ((comp f g).arity-2) :=
begin
  intros hF hG z n, rw comp_arity_eq,
  have H := comp_fwd_def _ _ _ _ hF hG,
  simp [comp, ev, *]
end

def prec_loop (g : RPP) :=
  Id 2 ‖ mkpair ;;
  Id 1 ‖ mkpair ;;
  Id 1 ‖ (Sw ;; g) ;;
  Id 2 ‖ unpair ;;
  Id 3 ‖ unpair ;;
  ⌊2, 3, 1, 0, 4⌉ ;;
  Id 1 ‖ Su ‖ Id 1 ‖ mkpair ;;
  ⌊3, 0, 1, 2⌉

def prec_fwd (f g : RPP) :=
  Id 1 ‖ unpair ;;
  ⌊0, 2, 3, 1⌉ ;;
  Id 2 ‖ f ;;
  ⌊0, 1, 4, 3, 5, 2⌉ ;;
  Id 1 ‖ It (prec_loop g) ;;
  ⌊5, 0⌉

lemma prec_fwd_arity_le1 (f g : RPP) : 12 ≤ (prec_fwd f g).arity :=
begin
  rw [prec_fwd, prec_loop], simp,
  left, right, rw [show 12 = 1 + (10 + 1), by refl], simp
end

lemma prec_fwd_arity_le2 (f g : RPP) : f.arity + 2 ≤ (prec_fwd f g).arity :=
begin
  rw [prec_fwd, prec_loop], simp,
  left, left, left, right, rw add_comm
end

lemma prec_fwd_arity_le3 (f g : RPP) : g.arity + 3 ≤ (prec_fwd f g).arity :=
begin
  rw [prec_fwd, prec_loop], simp,
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

lemma prec_loop_def (F G : ℕ → ℕ) (f g : RPP) : ex_rpp G g → ∀ (Z N s : ℕ), ∃ (s' : ℕ),
  ‹prec_loop g› (s :: Z :: N :: nat.prec_loop F G Z N :: repeat 0 ((prec_fwd f g).arity-6)) =
  s' :: Z :: (N + 1) :: nat.prec_loop F G Z (N + 1) :: repeat 0 ((prec_fwd f g).arity-6) :=
begin
  intros hG Z N s, use nat.mkpair s (nat.prec_loop F G Z N),
  rcases prec_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁,
  have HG := ex_rpp_le _ _ hG _ h₃, clear hG,
  simp [prec_loop, nat.prec_loop, ev, rewire, *] at *
end

lemma it_prec_loop_def (F G : ℕ → ℕ) (f g : RPP) : ex_rpp G g → ∀ (Z N : ℕ), ∃ (s : ℕ),
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
  ex_rpp F f → ex_rpp G g → ∀ (n : ℕ), ∃ (s : ℕ), ∀ (z : ℤ),
  ‹prec_fwd f g› (z :: n :: repeat 0 ((prec_fwd f g).arity-2)) =
  nat.prec_loop F G (nat.unpair n).fst (nat.unpair n).snd ::
    z :: (nat.unpair n).snd :: s :: (nat.unpair n).fst :: (nat.unpair n).snd ::
    repeat 0 ((prec_fwd f g).arity-6) :=
begin
  intros hF hG n,
  rcases prec_fwd_arity f g with ⟨a, h₁, h₂, h₃⟩, rw h₁ at *,
  have HF := ex_rpp_le _ _ hF _ h₂, clear hF,
  have h := it_prec_loop_def F G f g hG (nat.unpair n).fst (nat.unpair n).snd,
  rcases h with ⟨s, h⟩, use s, intro z,
  simp [prec_fwd, ev, rewire, *] at *
end

def prec (f g : RPP) := prec_fwd f g ;; inc ;; (prec_fwd f g)⁻¹

lemma prec_arity_eq (f g : RPP) : (prec f g).arity = (prec_fwd f g).arity :=
begin
  rw prec, simp [rewire, arity_inv],
  have h := prec_fwd_arity_le1 f g, linarith
end

lemma prec_def (F G : ℕ → ℕ) (f g : RPP) : ex_rpp F f → ex_rpp G g → ∀ (z : ℤ) (n : ℕ),
  ‹prec f g› (z :: n :: repeat 0 ((prec f g).arity-2)) =
  (z + nat.prec_loop F G (nat.unpair n).fst (nat.unpair n).snd) ::
    n :: repeat 0 ((prec f g).arity-2) :=
begin
  intros hF hG z n, rw prec_arity_eq,
  have h := prec_fwd_def _ _ _ _ hF hG n, rcases h with ⟨s, h⟩,
  simp [prec, ev, *]
end

theorem completeness (F : ℕ → ℕ) : nat.primrec F → ∃ f, ex_rpp F f :=
begin
  intro h, induction h,
  case zero : { use Id 0, simp [ex_rpp, ev] },
  case succ : { use succ, exact succ_def },
  case left : { use left, exact left_def },
  case right : { use right, exact right_def },
  case pair : G₁ G₂ h₁ h₂ ih₁ ih₂
  { rcases ih₁ with ⟨g₁, ih₁⟩, rcases ih₂ with ⟨g₂, ih₂⟩,
    use pair g₁ g₂, rw ex_rpp, exact pair_def _ _ _ _ ih₁ ih₂ },
  case comp : G₁ G₂ h₁ h₂ ih₁ ih₂
  { rcases ih₁ with ⟨g₁, ih₁⟩, rcases ih₂ with ⟨g₂, ih₂⟩,
    use comp g₁ g₂, rw ex_rpp, exact comp_def _ _ _ _ ih₁ ih₂ },
  case prec : G₁ G₂ h₁ h₂ ih₁ ih₂
  { rcases ih₁ with ⟨g₁, ih₁⟩, rcases ih₂ with ⟨g₂, ih₂⟩,
    use prec g₁ g₂, rw ex_rpp, exact prec_def _ _ _ _ ih₁ ih₂ }
end

end RPP