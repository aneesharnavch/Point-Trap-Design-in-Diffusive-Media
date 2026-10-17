module

public import TimeTraps.Probability.BrownianQuadraticVariationStopped

@[expose] public section

/-! Whole-sequence almost-sure convergence of stopped dyadic quadratic
variation, first at one fixed time and then simultaneously at the
countably many dyadic grid nodes of a fixed compact horizon. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianStoppedDyadicQV_ae_tendsto (hB : IsPreBrownianReal B P) (T s : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => brownianStoppedDyadicQV B T n s ω) atTop (𝓝 (min s T).val) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hs : Summable (fun n => ∫ ω,
      (brownianStoppedDyadicQV B T n s ω - (min s T).val) ^ 2 ∂P) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => sq_nonneg _))
      (brownianStoppedDyadicQV_l2_error_le hB T s)
    simpa only [div_eq_mul_inv, inv_pow, one_mul] using
      (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left (2 * T.val ^ 2)
  have he := ae_tendsto_zero_of_summable_integral_sq
    (fun n ω => brownianStoppedDyadicQV B T n s ω - (min s T).val)
    (fun n => (brownianPartitionQV_memLp hB (brownianStoppedDyadicGrid T s n)).sub
      (memLp_const (min s T).val)) hs
  filter_upwards [he] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add_const (min s T).val

theorem brownianStoppedDyadicQV_grid_ae_tendsto (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ i : Fin (2 ^ m + 1),
      Tendsto (fun n => brownianStoppedDyadicQV B T n (brownianDyadicGrid T m i) ω)
        atTop (𝓝 (brownianDyadicGrid T m i).val) := by
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro i
  have ht := brownianStoppedDyadicQV_ae_tendsto hB T (brownianDyadicGrid T m i)
  simpa only [min_eq_left (brownianDyadicGrid_mem_Icc T m i).2] using ht

end TimeTraps.Probability
