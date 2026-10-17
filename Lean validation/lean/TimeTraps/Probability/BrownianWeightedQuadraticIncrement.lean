module

public import TimeTraps.Probability.BrownianQuadraticVariationMoments
public import TimeTraps.Probability.BrownianStepIntegralIncrement

@[expose] public section

/-! Centered squared Brownian increments: exact second moment and
conditional centering against the entire raw past filtration. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianCompensatedSquareIncrement (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  (B t ω - B s ω) ^ 2 - (t.val - s.val)

theorem brownianCompensatedSquareIncrement_memLp (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    MemLp (brownianCompensatedSquareIncrement B s t) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownian_increment_square_memLp hB s t).sub (memLp_const (t.val - s.val))

theorem brownianCompensatedSquareIncrement_mean (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, brownianCompensatedSquareIncrement B s t ω ∂P) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  change (∫ ω, (B t ω - B s ω) ^ 2 - (t.val - s.val) ∂P) = 0
  rw [integral_sub (brownian_increment_integrable_sq hB s t) (integrable_const _),
    brownian_increment_second_moment hB, abs_of_nonneg (sub_nonneg.mpr (show s.val ≤ t.val from hst))]
  simp

theorem brownianCompensatedSquareIncrement_secondMoment (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, brownianCompensatedSquareIncrement B s t ω ^ 2 ∂P) = 2 * (t.val - s.val) ^ 2 := by
  have hv := variance_eq_integral (brownian_increment_square_memLp hB s t).aemeasurable
  rw [brownian_increment_second_moment hB,
    abs_of_nonneg (sub_nonneg.mpr (show s.val ≤ t.val from hst))] at hv
  calc
    _ = Var[fun ω => (B t ω - B s ω) ^ 2; P] := hv.symm
    _ = 2 * |t.val - s.val| ^ 2 := brownian_increment_square_variance hB s t
    _ = _ := by rw [sq_abs]

theorem brownianCompensatedSquareIncrement_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[brownianCompensatedSquareIncrement B s t | brownianNaturalFiltration B hBm s] =ᵐ[P] 0 := by
  have h := brownian_increment_function_condExp hB hBm hst
    (fun x => x ^ 2 - (t.val - s.val)) (by fun_prop)
  change P[brownianCompensatedSquareIncrement B s t | brownianNaturalFiltration B hBm s] =ᵐ[P]
    (fun _ => ∫ ω, brownianCompensatedSquareIncrement B s t ω ∂P) at h
  simpa only [brownianCompensatedSquareIncrement_mean hB hst, Pi.zero_def] using h

theorem brownian_adapted_indep_compensatedSquare (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) :
    IndepFun ξ (brownianCompensatedSquareIncrement B s t) P :=
  (brownian_adapted_indep_increment hB hBm hst hξ).comp measurable_id
    (show Measurable (fun x : ℝ => x ^ 2 - (t.val - s.val)) by fun_prop)

end TimeTraps.Probability
