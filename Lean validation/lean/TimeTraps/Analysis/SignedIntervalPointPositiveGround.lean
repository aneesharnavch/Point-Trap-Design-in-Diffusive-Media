module

public import TimeTraps.Analysis.SignedIntervalPointPositiveGroundRegularity
public import TimeTraps.Analysis.SignedIntervalPointPositiveGroundZeros
public import TimeTraps.Analysis.SignedIntervalPointMinimizerNonnegative

@[expose] public section

/-! The independently attained signed Rayleigh minimum has an actual
principal H1 eigenstate that is strictly positive throughout the closed
interval. Real eigenvalues and real contact strengths of either sign are
allowed. No eigenspace simplicity assertion is made in this file. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.nonnegative_minimizer_pos
    (P : SignedIntervalPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue)
    (hnonneg : ∀ x ∈ Icc l r, 0 ≤ u x) : ∀ x ∈ Icc l r, 0 < u x := by
  obtain ⟨n, Q, j, hj, ht⟩ := P.minimizer_linear_piecewise hu hm hmin
  intro x hx
  by_contra hn
  have hz : u x = 0 := le_antisymm (le_of_not_gt hn) (hnonneg x hx)
  have he := Q.eq_zero_of_nonnegative_zero hj ht hnonneg hx hz
  have hmzero : P.squareMass u = 0 := by
    calc
      P.squareMass u = ∫ _y in l..r, (0 : ℝ) ^ 2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le P.interval_pos.le
        intro y hy
        change u y ^ 2 = (0 : ℝ) ^ 2
        rw [he y (Ioo_subset_Icc_self hy)]
      _ = 0 := by simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero]
  exact hm.ne' hmzero

theorem SignedIntervalPointProblem.positive_principal_eigenstate
    (P : SignedIntervalPointProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ hu : IntervalEnergy u l r,
      (∀ x ∈ Icc l r, 0 < u x) ∧ 0 < P.squareMass u ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, u x * v x) ∧
      ((ofEnergy hu P.interval_pos).state,
        P.principalValue • (ofEnergy hu P.interval_pos).state) ∈ P.operator.graph := by
  obtain ⟨u, hu, hnonneg, hm, hmin⟩ := P.nonnegative_rayleigh_minimizer
  exact ⟨u, hu, P.nonnegative_minimizer_pos hu hm hmin (fun x _ => hnonneg x), hm,
    P.minimizer_weak hu hm hmin, P.minimizer_operator_graph hu hm hmin⟩

end TimeTraps.Analysis
