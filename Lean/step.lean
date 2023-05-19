import library
import tactic

open rpp

namespace rpp

def step (f : rpp) :=
  ⌊2, 0, 1⌉ ;;
  If Su Id₁ Id₁ ;;
  Sw ;;
  If (Pr ‖ Su) (Id₁ ‖ f ;; Sw) Id₁ ;;
  ⌊2, 0, 1⌉ ;;
  If Pr Id₁ Id₁ ;;
  Sw

lemma step_succ (f : rpp) (x y : ℕ) (z : list ℤ) :
  ‹step f› (0 :: x :: y.succ :: z) = 0 :: x.succ :: y :: z :=
by simp [step, ev, rewire]

lemma step_zero (f : rpp) (x : ℕ) (z : list ℤ) :
  ‹step f› (0 :: x :: 0 :: z) = 0 :: 0 :: ‹f› (x :: z) :=
begin
  rcases h : ‹f› (↑x :: z),
  { apply_fun list.length at h, simp * at * },
  { simp [step, ev, rewire, *] }
end

def cp_in :=
  inc ;;
  Id₁ ‖ It (Su ;; inc) ;;
  Id₁ ‖ dec ;;
  dec ;;
  ⌊0, 3, 1⌉ ;;
  inc ;;
  Id₁ ‖ Sw

def cu_in := It (step Su)

def cp :=
  cp_in ;;
  ⌊2, 3, 0, 1⌉ ;;
  cu_in⁻¹

def div := It (step (Id₁ ‖ Su))

end rpp