module

public import TimeTraps.Probability.BrownianQuadraticVariation
public import TimeTraps.Analysis.SummableSquareError

@[expose] public section

/-! The exact geometric squared-error bound yields almost-sure convergence
of the entire dyadic quadratic-variation sequence at every fixed horizon.
The horizon is fixed before the exceptional event; a common event is also
provided for any specified countable sequence of horizons. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianDyadicQV_ae_tendsto (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => brownianDyadicQV B T n ω) atTop (𝓝 T.val) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hs : Summable (fun n => ∫ ω, (brownianDyadicQV B T n ω - T.val) ^ 2 ∂P) := by
    simp only [brownianDyadicQV_l2_error hB T]
    simpa only [div_eq_mul_inv, inv_pow, one_mul] using
      (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left (2 * T.val ^ 2)
  have he := ae_tendsto_zero_of_summable_integral_sq
    (fun n ω => brownianDyadicQV B T n ω - T.val)
    (fun n => (brownianPartitionQV_memLp hB (brownianDyadicGrid T n)).sub (memLp_const T.val)) hs
  filter_upwards [he] with ω hω
  have ht := hω.add_const T.val
  simpa only [sub_add_cancel, zero_add] using ht

theorem brownianDyadicQV_countable_horizons_ae (hB : IsPreBrownianReal B P) (T : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      Tendsto (fun n => brownianDyadicQV B (T k) n ω) atTop (𝓝 (T k).val) :=
  ae_all_iff.mpr (fun k => brownianDyadicQV_ae_tendsto hB (T k))

end TimeTraps.Probability
