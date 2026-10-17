module

public import TimeTraps.Interval.WeightedGridIFTNonlinearResidual
public import TimeTraps.Interval.WeightedGridIFTValueEnvelope

@[expose] public section

/-! The actual nonlinear family's attained minimum has the same first-order
envelope coefficient. The argument needs only a uniform O(ε²) weight error. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

variable {n : ℕ}

theorem gridIFT_nonlinear_minimum_value_expansion (W : ℝ → CellWeight) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)
    (hexp : SourceUniformExpansion (fun ε => (W ε).value) (fun _ => Ω) (fun z => Ω * h z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost (W ε) ≤ P.gridCost (W ε)) →
      |Q.gridCost (W ε) - Ω / (12 * ((n : ℝ) + 1) ^ 2) -
        ε * gridIFTValueCoefficient h Ω n| ≤ C * ε ^ 2 := by
  obtain ⟨B, hB, hrem⟩ := hexp
  obtain ⟨C, δ, hC, hδ, hex⟩ := gridIFT_minimum_value_expansion (n := n) h hh Ω hΩ
  obtain ⟨η, hη, hw⟩ := gridIFT_affine_weight_exists h hh.continuousOn Ω hΩ
  have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < min δ η := by
    have ht : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ∈ Metric.ball (0 : ℝ) (min δ η) :=
      Metric.ball_mem_nhds 0 (lt_min hδ hη)
    exact ht.mono (fun _ he => by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he)
  refine ⟨B + C, by positivity, ?_⟩
  filter_upwards [hrem, hsmall] with ε hremε hε
  intro Q hQ
  obtain ⟨V, hV⟩ := hw ε (lt_of_lt_of_le hε (min_le_right δ η))
  obtain ⟨R, hR⟩ := ClosedPartition.grid_minimum_exists V (Nat.succ_pos n)
  have hdiff := weighted_grid_minimum_cost_perturbation Q R (W ε) V
    (δ := B * ε ^ 2) (fun z hz => ?_) hQ hR
  · have hval := hex ε (lt_of_lt_of_le hε (min_le_left δ η)) V hV R hR
    calc
      _ = |(Q.gridCost (W ε) - R.gridCost V) +
          (R.gridCost V - Ω / (12 * ((n : ℝ) + 1) ^ 2) -
            ε * gridIFTValueCoefficient h Ω n)| := by congr 1; ring
      _ ≤ |Q.gridCost (W ε) - R.gridCost V| +
          |R.gridCost V - Ω / (12 * ((n : ℝ) + 1) ^ 2) -
            ε * gridIFTValueCoefficient h Ω n| := abs_add_le _ _
      _ ≤ (B + C) * ε ^ 2 := by nlinarith
  · rw [hV z hz]
    have he : (W ε).value z - Ω * (1 + ε * h z) =
        (W ε).value z - Ω - ε * (Ω * h z) := by ring
    rw [he]
    exact hremε z hz

end TimeTraps.Interval
