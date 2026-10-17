module

public import TimeTraps.Interval.WeightedGridCompact

@[expose] public section

/-! Uniform perturbation bounds for the actual nearest-grid objective.
The same error estimate holds for every closed grid, including repeated
nodes. The affine specialization leaves the perturbation profile signed. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ}

theorem ClosedPartition.gridCost_weight_perturbation (Q : ClosedPartition n) (W V : CellWeight)
    {δ : ℝ} (h : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ δ) :
    |Q.gridCost W - Q.gridCost V| ≤ δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (h 0 ⟨le_rfl, zero_le_one⟩)
  have hb := intervalIntegral.norm_integral_le_of_norm_le (f := fun x =>
      W.value x * gridDistance Q.point x ^ 2 - V.value x * gridDistance Q.point x ^ 2)
    zero_le_one (Filter.Eventually.of_forall (fun x hx => ?_))
    (show IntervalIntegrable (fun _ : ℝ => δ) volume 0 1 from intervalIntegrable_const)
  · rw [intervalIntegral.integral_sub (Q.gridCost_integrable W) (Q.gridCost_integrable V),
      Real.norm_eq_abs] at hb
    simpa only [ClosedPartition.gridCost, intervalIntegral.integral_const, sub_zero,
      one_smul] using hb
  · have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hd := Q.gridDistance_le_one hx'
    have hn := gridDistance_nonneg Q.point x
    rw [← sub_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg (gridDistance Q.point x))]
    calc
      _ ≤ δ * gridDistance Q.point x ^ 2 := mul_le_mul_of_nonneg_right (h x hx') (sq_nonneg _)
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (by nlinarith) hδ
      _ = δ := mul_one δ

theorem ClosedPartition.gridCost_affine_perturbation (Q : ClosedPartition n) (W V : CellWeight)
    {Ω ε H : ℝ} {h : ℝ → ℝ} (hΩ : 0 < Ω)
    (hV : ∀ x ∈ Icc (0 : ℝ) 1, V.value x = Ω)
    (hW : ∀ x ∈ Icc (0 : ℝ) 1, W.value x = Ω * (1 + ε * h x))
    (hh : ∀ x ∈ Icc (0 : ℝ) 1, |h x| ≤ H) :
    |Q.gridCost W - Q.gridCost V| ≤ |ε| * Ω * H := by
  apply Q.gridCost_weight_perturbation W V
  intro x hx
  rw [hW x hx, hV x hx]
  have he : Ω * (1 + ε * h x) - Ω = ε * Ω * h x := by ring
  rw [he, abs_mul, abs_mul, abs_of_pos hΩ]
  exact mul_le_mul_of_nonneg_left (hh x hx) (mul_nonneg (abs_nonneg _) hΩ.le)

theorem weighted_grid_minimum_cost_perturbation (Q R : ClosedPartition n) (W V : CellWeight)
    {δ : ℝ} (h : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ δ)
    (hQ : ∀ P : ClosedPartition n, Q.gridCost W ≤ P.gridCost W)
    (hR : ∀ P : ClosedPartition n, R.gridCost V ≤ P.gridCost V) :
    |Q.gridCost W - R.gridCost V| ≤ δ := by
  have h₁ := abs_le.mp (Q.gridCost_weight_perturbation W V h)
  have h₂ := abs_le.mp (R.gridCost_weight_perturbation W V h)
  exact abs_le.mpr ⟨by linarith [hR Q], by linarith [hQ R]⟩

end TimeTraps.Interval
