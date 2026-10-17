module

public import TimeTraps.Spectral.RobinStrengthComparison
public import TimeTraps.Spectral.StrengthSplitting

@[expose] public section

/-! Positive splitting with unchanged total interior strength and unchanged
Robin boundary coefficients. The additional trap is independently placeable. -/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {n : ℕ}

noncomputable def RobinPlacementProblem.split (C : RobinPlacementProblem n) (j : Fin n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : RobinPlacementProblem (n + 1) where
  toPlacementProblem := C.toPlacementProblem.split j a b ha hb
  betaLeft := C.betaLeft
  betaLeft_nonneg := C.betaLeft_nonneg
  betaRight := C.betaRight
  betaRight_nonneg := C.betaRight_nonneg

theorem RobinPlacementProblem.split_total (C : RobinPlacementProblem n) (j : Fin n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = C.strength j) :
    (∑ i, (C.split j a b ha hb).strength i) = ∑ i, C.strength i :=
  splitStrength_sum C.strength j hab

theorem RobinPlacementProblem.split_root_lt (C : RobinPlacementProblem n) (j : Fin n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = C.strength j) :
    C.root < (C.split j a b ha hb).root := by
  apply C.root_lt_of_phase_sum_lt (C.split j a b ha hb) rfl rfl rfl rfl
  intro k hk
  have hc : 0 < 2 * C.diffusivity * k := mul_pos (mul_pos (by norm_num) C.diffusivity_pos) hk
  have hs := scaledArctan_split_lt hc ha hb
  rw [hab] at hs
  have ht := splitStrength_map_sum (scaledArctan (2 * C.diffusivity * k)) C.strength j a b
  change (∑ i, scaledArctan (2 * C.diffusivity * k) (C.strength i)) <
    ∑ i, scaledArctan (2 * C.diffusivity * k) (splitStrength C.strength j a b i)
  rw [ht]
  linarith

end TimeTraps.Spectral
