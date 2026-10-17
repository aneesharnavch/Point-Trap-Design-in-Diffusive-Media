module

public import TimeTraps.Spectral.BudgetAsymptoticLimits
public import TimeTraps.Spectral.InversePhaseExpansion
public import Mathlib.Tactic.Field

@[expose] public section

/-! The manuscript's spectral expansion with its full order-six count remainder.
All coefficients and remainder transformations are exact real algebra. -/

namespace TimeTraps.Spectral

open Set Filter Topology Asymptotics

/-- Fixed total K, D, L: the remainder is O(N^-6), through the natural counts. -/
theorem spectralBudgetValue_many_traps_expansion {D L K : ℝ}
    (hD : 0 < D) (hL : 0 < L) (hK : 0 < K) :
    (fun n : ℕ => spectralBudgetValue n D L K -
      (K / L - K ^ 2 / (12 * D * (n : ℝ) ^ 2) +
        K ^ 3 * L / (180 * D ^ 2 * (n : ℝ) ^ 4)))
      =O[atTop] (fun n => 1 / (n : ℝ) ^ 6) := by
  have hi := budgetPhase_inverse_expansion.comp_tendsto
    (spectral_parameter_many_traps_limit hD hL hK)
  have hm := hi.mul (isBigO_refl (fun n : ℕ => 4 * D * (n : ℝ) ^ 2 / L ^ 2) atTop)
  have h : (fun n : ℕ => spectralBudgetValue n D L K -
      (K / L - K ^ 2 / (12 * D * (n : ℝ) ^ 2) +
        K ^ 3 * L / (180 * D ^ 2 * (n : ℝ) ^ 4)))
      =O[atTop] (fun n => (K ^ 4 * L ^ 2 / (64 * D ^ 3)) * (1 / (n : ℝ) ^ 6)) := by
    apply hm.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
      dsimp [Function.comp_def, spectralBudgetValue]
      field [ne_of_gt hD, ne_of_gt hL, hnR]
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
      dsimp [Function.comp_def]
      field [ne_of_gt hD, ne_of_gt hL, hnR]
  exact h.of_const_mul_right

/-- Fixed N, D, L: the same inverse series gives the weak-budget O(K^4) remainder. -/
theorem spectralBudgetValue_weak_expansion {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    (fun K : ℝ => spectralBudgetValue n D L K -
      (K / L - K ^ 2 / (12 * D * (n : ℝ) ^ 2) +
        K ^ 3 * L / (180 * D ^ 2 * (n : ℝ) ^ 4)))
      =O[𝓝[>] 0] (fun K => K ^ 4) := by
  have hi := budgetPhase_inverse_expansion.comp_tendsto
    (spectral_parameter_weak_limit hn hD hL)
  have hm := hi.mul (isBigO_refl (fun _ : ℝ => 4 * D * (n : ℝ) ^ 2 / L ^ 2) (𝓝[>] 0))
  have h : (fun K : ℝ => spectralBudgetValue n D L K -
      (K / L - K ^ 2 / (12 * D * (n : ℝ) ^ 2) +
        K ^ 3 * L / (180 * D ^ 2 * (n : ℝ) ^ 4)))
      =O[𝓝[>] 0] (fun K => (L ^ 2 / (64 * D ^ 3 * (n : ℝ) ^ 6)) * K ^ 4) := by
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    apply hm.congr
    · intro K
      dsimp [Function.comp_def, spectralBudgetValue]
      field [ne_of_gt hD, ne_of_gt hL, hnR]
    · intro K
      dsimp [Function.comp_def]
      field [ne_of_gt hD, ne_of_gt hL, hnR]
  exact h.of_const_mul_right

end TimeTraps.Spectral
