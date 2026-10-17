module

public import TimeTraps.Interval.WeightedGridIFTValue

@[expose] public section

/-! The attained minimum has the displayed envelope derivative and an
O(ε²) expansion. These follow from the checked variational remainder. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

variable {n : ℕ} (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)

theorem gridIFTValue_expansion :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ →
      |gridIFTValue (n := n) h hh Ω hΩ ε - Ω / (12 * ((n : ℝ) + 1) ^ 2) -
        ε * gridIFTValueCoefficient h Ω n| ≤ C * ε ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hexp⟩ := gridIFT_minimum_value_expansion (n := n) h hh Ω hΩ
  obtain ⟨η, hη, hatt⟩ := gridIFTValue_attained (n := n) h hh Ω hΩ
  refine ⟨C, min δ η, hC, lt_min hδ hη, ?_⟩
  intro ε hε
  obtain ⟨W, hW, hv⟩ := hatt ε (lt_of_lt_of_le hε (min_le_right δ η))
  obtain ⟨Q, hQ⟩ := hv.1
  dsimp only at hQ
  have hmin : ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W := by
    intro P
    rw [hQ]
    exact hv.2 ⟨P, rfl⟩
  simpa only [hQ] using hexp ε (lt_of_lt_of_le hε (min_le_left δ η)) W hW Q hmin

theorem gridIFTValue_derivative :
    HasDerivAt (gridIFTValue (n := n) h hh Ω hΩ) (gridIFTValueCoefficient h Ω n) 0 := by
  obtain ⟨C, δ, _, hδ, hb⟩ := gridIFTValue_expansion (n := n) h hh Ω hΩ
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < δ := by
    have ht : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds 0 hδ
    filter_upwards [ht] with ε hε
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  have ho : (fun ε => gridIFTValue (n := n) h hh Ω hΩ ε -
      gridIFTValue (n := n) h hh Ω hΩ 0 - ε * gridIFTValueCoefficient h Ω n) =O[𝓝 (0 : ℝ)]
      (fun ε => ε ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [he] with ε hε
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε), gridIFTValue_zero] using hb ε hε
  apply hasDerivAt_iff_isLittleO.mpr
  simpa only [sub_zero, smul_eq_mul] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num : 1 < (2 : ℕ)))

theorem gridIFTValue_deriv :
    deriv (gridIFTValue (n := n) h hh Ω hΩ) 0 = gridIFTValueCoefficient h Ω n :=
  (gridIFTValue_derivative h hh Ω hΩ).deriv

end TimeTraps.Interval
