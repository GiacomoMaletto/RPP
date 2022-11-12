import basic
import computability.primrec
import logic.denumerable
import tactic

open primrec list RPP sum equiv

namespace list

lemma reverse_drop {α : Type*} (n : ℕ) (l : list α) :
  (l.drop n) = reverse (l.reverse.take (l.length - n)) :=
begin
  rw [reverse_take (l.length - n), reverse_reverse],
  cases (le_or_lt l.length n),
  simp *,
  congr; omega,
  omega
end

end list

namespace primrec

variables {α : Type*} {β : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable σ]

lemma int_of_nat : primrec int.of_nat := 
encode_iff.mp $ nat_bit0.of_eq $ λ n, by refl

lemma int_neg_succ_of_nat : primrec int.neg_succ_of_nat :=
encode_iff.mp $ nat_bit1.of_eq $ λ n, by refl

private def F :=  equiv.int_equiv_nat_sum_nat.trans (equiv.bool_prod_equiv_sum ℕ).symm
def G := equiv.int_equiv_nat.trans equiv.bool_prod_nat_equiv_nat.symm

private lemma int_G : primrec G :=
encode_iff.mp $ nat_bodd_div2.of_eq $ λ n, by { simp [G] }

private lemma int_F : primrec F := int_G.of_eq $ λ a,
begin
 rw [G, int_equiv_nat, nat_sum_nat_equiv_nat],
 rw [trans_apply, trans_apply, trans_apply],
 rw [symm_apply_apply], refl
end

lemma int_cases {f : α → ℤ} {g h : α → ℕ → β}
  (hf : primrec f) (hg : primrec₂ g) (hh : primrec₂ h) :
  @primrec _ β _ _ (λ a, int.cases_on (f a) (g a) (h a)) :=
(cond (fst.comp $ int_F.comp $ hf)
  (hh.comp primrec.id (snd.comp $ int_F.comp $ hf))
  (hg.comp primrec.id (snd.comp $ int_F.comp $ hf))).of_eq $
λ a, by cases f a; refl

lemma int_neg_of_nat : primrec int.neg_of_nat :=
(nat_cases primrec.id (const 0) (int_neg_succ_of_nat.comp $ snd).to₂).of_eq $
λ n, by cases n; refl

lemma int_sub_nat_nat : primrec₂ int.sub_nat_nat :=
(nat_cases (nat_sub.comp snd fst)
  (int_of_nat.comp $ nat_sub.comp fst snd)
  (int_neg_succ_of_nat.comp snd).to₂).to₂.of_eq $
λ m n, by rw int.sub_nat_nat; cases n - m; refl

lemma int_neg : primrec int.neg :=
(int_cases primrec.id (int_neg_of_nat.comp snd).to₂
  (int_of_nat.comp $ succ.comp snd).to₂).of_eq $
λ n, by cases n; refl 

lemma int_add : primrec₂ int.add :=
(int_cases fst (int_cases (snd.comp fst)
  (int_of_nat.comp $ nat_add.comp (snd.comp fst) snd).to₂
  (int_sub_nat_nat.comp (snd.comp fst) (succ.comp snd)).to₂).to₂
  (int_cases (snd.comp fst)
  (int_sub_nat_nat.comp snd (succ.comp $ snd.comp fst)).to₂
  (int_neg_succ_of_nat.comp $ succ.comp $ nat_add.comp
  (snd.comp fst) snd).to₂).to₂).to₂.of_eq $
λ m n, by cases m; cases n; refl

lemma int_sub : primrec₂ int.sub :=
(int_add.comp fst (int_neg.comp snd)).to₂.of_eq $
λ m n, by refl

lemma int_succ : primrec int.succ :=
(int_add.comp primrec.id (const 1)).of_eq $
λ n, by refl

lemma int_pred : primrec int.pred :=
(int_sub.comp primrec.id (const 1)).of_eq $
λ n, by refl

lemma int_to_nat : primrec int.to_nat :=
(int_cases primrec.id snd.to₂ (const 0).to₂).of_eq $
λ n, by cases n; refl

private def take2 {α : Type*} (n : ℕ) (l : list α) :=
list.foldl
  (λ (x : ℕ × list α) a, nat.cases x (λ m, (m, a :: x.snd)) x.fst)
  (n, []) l

private lemma list_take2 : primrec₂ (@take2 α) :=
(list_foldl snd (pair fst (const []))
  (nat_cases (fst.comp $ fst.comp snd) (fst.comp snd)
  (pair snd (list_cons.comp (snd.comp $ snd.comp fst)
  (snd.comp $ fst.comp $ snd.comp fst))).to₂).to₂).to₂.of_eq $
λ n l, by refl

private lemma take2_take (n : ℕ) (l : list α) :
  take2 n l = (n - l.length, (take n l).reverse) :=
begin
  induction l using list.reverse_rec_on with l x hl,
  simp [take2],
  cases (lt_or_le l.length n),

  have h₁ : (l ++ [x]).length ≤ n := by simp; omega,
  rw [take_all_of_le h₁, reverse_append, length_append],
  rw take_all_of_le (le_of_lt h) at hl,
  unfold take2 at *, rw foldl_append,
  simp only [hl, foldl_cons, foldl_nil],
  have h₃ : ∃ m : ℕ, n - l.length = m.succ :=
  by apply nat.exists_eq_succ_of_ne_zero; omega,
  rcases h₃ with ⟨m, hm⟩,
  simp *; omega,

  have h₁ : n - l.length = 0 := tsub_eq_zero_of_le h,
  rw h₁ at hl,
  have h₂ : n - (l ++ [x]).length = 0 := by simp; omega,
  rw h₂,
  unfold take2 at *,
  simp [foldl_append, take_append_eq_append_take, *]
end

lemma list_take : primrec₂ (@list.take α) :=
(list_reverse.comp (snd.comp list_take2)).to₂.of_eq $
λ n l, by rw take2_take; simp

lemma list_drop : primrec₂ (@list.drop α) :=
(list_reverse.comp (list_take.comp (nat_sub.comp (list_length.comp snd) fst)
  (list_reverse.comp snd))).to₂.of_eq $
λ n l, by rw list.reverse_drop


lemma rpp_id (n : ℕ) : primrec ‹Id n› := by apply primrec.id

lemma rpp_ne : primrec ‹Ne› :=
(list_cases primrec.id (const [])
  (list_cons.comp (int_neg.comp $ fst.comp snd) (snd.comp snd)).to₂).of_eq $
λ l, by cases l; refl

lemma rpp_su : primrec ‹Su› :=
(list_cases primrec.id (const [])
  (list_cons.comp (int_succ.comp $ fst.comp snd) (snd.comp snd)).to₂).of_eq $
λ l, by cases l; refl

lemma rpp_pr : primrec ‹Pr› :=
(list_cases primrec.id (const [])
  (list_cons.comp (int_pred.comp $ fst.comp snd) (snd.comp snd)).to₂).of_eq $
λ l, by cases l; refl

lemma rpp_sw : primrec ‹Sw› :=
(list_cases primrec.id (const [])
  (list_cases (snd.comp snd) (list_cons.comp (fst.comp snd) (const []))
  (list_cons.comp (fst.comp snd) (list_cons.comp (fst.comp $ snd.comp fst) (snd.comp snd)))
  .to₂).to₂).of_eq $
λ l, by {cases l with _ l', refl, cases l'; refl}

lemma rpp_co {f g : RPP} (hf : primrec ‹f›) (hg : primrec ‹g›) : primrec ‹f ;; g› :=
(comp hg hf).of_eq $ λ l, by refl

lemma rpp_pa {f g : RPP} (hf : primrec ‹f›) (hg : primrec ‹g›) : primrec ‹f ‖ g› :=
(list_append.comp
  (comp hf (list_take.comp (const f.arity) primrec.id))
  (comp hg (list_drop.comp (const f.arity) primrec.id))).of_eq $
λ l, by refl

lemma rpp_it {f : RPP} (hf : primrec ‹f›) : primrec ‹It f› :=
(list_cases primrec.id (const [])
  (list_cons.comp (fst.comp snd) ((nat_iterate (int_to_nat.comp $ fst.comp snd)
  (snd.comp snd) (hf.comp snd).to₂))).to₂).of_eq $
λ l, by cases l; refl

lemma rpp_if {f g h : RPP} (hf : primrec ‹f›) (hg : primrec ‹g›) (hh : primrec ‹h›) :
  primrec ‹If f g h› :=
(list_cases primrec.id (const [])
  (list_cons.comp (fst.comp snd)
  (int_cases (fst.comp snd)
  (nat_cases snd (hg.comp $ snd.comp $ snd.comp fst)
  (hf.comp $ snd.comp $ snd.comp $ fst.comp fst).to₂).to₂
  (hh.comp $ snd.comp $ snd.comp $ fst).to₂)).to₂).of_eq $
λ l, by {cases l with n, refl, cases n with n n, cases n; refl, refl}

theorem rpp_primrec (f : RPP) : primrec ‹f› :=
RPP.rec rpp_id rpp_ne rpp_su rpp_pr rpp_sw @rpp_co @rpp_pa @rpp_it @rpp_if f

end primrec