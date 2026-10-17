module

public import TimeTraps.Interval.WeightedGridPerturbationCompact

@[expose] public section

/-! The affine perturbation family from the near-homogeneous expansion.
Only the actual perturbed weight needs to be positive. The signed profile
is bounded on the unit interval; no positivity for all parameter values
or choice of a minimizing branch is built into the hypotheses. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ}

theorem ClosedPartition.gridCost_affine_difference (Q : ClosedPartition n) (W V : CellWeight)
    {Ω ε : ℝ} {h : ℝ → ℝ}
    (hV : ∀ x ∈ Icc (0 : ℝ) 1, V.value x = Ω)
    (hW : ∀ x ∈ Icc (0 : ℝ) 1, W.value x = Ω * (1 + ε * h x)) :
    Q.gridCost W - Q.gridCost V =
      ε * Ω * ∫ x in (0 : ℝ)..1, h x * gridDistance Q.point x ^ 2 := by
  unfold ClosedPartition.gridCost
  rw [← intervalIntegral.integral_sub (Q.gridCost_integrable W) (Q.gridCost_integrable V),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
  dsimp only
  rw [hW x hx', hV x hx']
  ring

theorem weighted_grid_affine_minimizers_near_uniform (V : CellWeight) (hn : 0 < n)
    {Ω H : ℝ} {h : ℝ → ℝ} (hΩ : 0 < Ω)
    (hV : ∀ x ∈ Icc (0 : ℝ) 1, V.value x = Ω)
    (hh : ∀ x ∈ Icc (0 : ℝ) 1, |h x| ≤ H)
    (U : Set (ClosedPartition n)) (hU : IsOpen U)
    (h₀ : (StrictPartition.uniform n hn).closed ∈ U) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, |ε| < η → ∀ W : CellWeight,
      (∀ x ∈ Icc (0 : ℝ) 1, W.value x = Ω * (1 + ε * h x)) →
      ∀ Q : ClosedPartition n, (∀ P : ClosedPartition n, Q.gridCost W ≤ P.gridCost W) → Q ∈ U := by
  obtain ⟨δ, hδ, hnear⟩ := weighted_grid_minimizers_near_uniform V hn hΩ hV U hU h₀
  have hH : 0 ≤ H := (abs_nonneg _).trans (hh 0 ⟨le_rfl, zero_le_one⟩)
  have hden : 0 < Ω * (H + 1) := mul_pos hΩ (by linarith)
  refine ⟨δ / (Ω * (H + 1)), div_pos hδ hden, ?_⟩
  intro ε hε W hW Q hQ
  apply hnear W ?_ Q hQ
  intro x hx
  rw [hW x hx, hV x hx]
  have he : Ω * (1 + ε * h x) - Ω = ε * Ω * h x := by ring
  rw [he, abs_mul, abs_mul, abs_of_pos hΩ]
  calc
    |ε| * Ω * |h x| ≤ |ε| * Ω * H :=
      mul_le_mul_of_nonneg_left (hh x hx) (mul_nonneg (abs_nonneg _) hΩ.le)
    _ ≤ |ε| * (Ω * (H + 1)) := by
      have hp := mul_nonneg (abs_nonneg ε) hΩ.le
      nlinarith
    _ ≤ δ := ((lt_div_iff₀ hden).mp hε).le

end TimeTraps.Interval
