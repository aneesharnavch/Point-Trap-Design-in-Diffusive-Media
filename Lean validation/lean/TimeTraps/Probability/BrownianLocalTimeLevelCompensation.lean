module

public import TimeTraps.Probability.BrownianLocalTimeLevelSign
public import TimeTraps.Probability.BrownianTanakaCompensation

@[expose] public section

/-! Shifted absolute Brownian differences are 2-Lipschitz in their level
in actual L². Combining this bound with sign-integral level continuity
gives continuity of the constructed compensation in L². It does not
select a pointwise version continuous in the spatial level. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaDifference_level_bound (B : ℝ≥0 → Ω → ℝ) (a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    |brownianTanakaDifference B a T ω - brownianTanakaDifference B b T ω| ≤ 2 * |a - b| := by
  have hf (x : ℝ) : |abs (x - a) - abs (x - b)| ≤ |a - b| := by
    calc
      _ ≤ |(x - a) - (x - b)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |a - b| := by
        rw [show (x - a) - (x - b) = -(a - b) by ring, abs_neg]
  exact brownianTanakaApproxDifference_error_le B (F := fun x => abs (x - a)) (a := b) hf T ω

theorem brownianTanakaDifferenceL2_level_bound (hB : IsPreBrownianReal B P) (a b : ℝ) (T : ℝ≥0) :
    ‖brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T) -
      brownianTanakaDifferenceL2 B b T (brownianTanakaDifference_memLp hB b T)‖ ≤ 2 * |a - b| := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A := brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T)
  let C := brownianTanakaDifferenceL2 B b T (brownianTanakaDifference_memLp hB b T)
  have hb : ∀ᵐ ω ∂P, ‖(A - C) ω‖ ≤ 2 * |a - b| := by
    filter_upwards [Lp.coeFn_sub A C,
      brownianTanakaDifferenceL2_coe B a T (brownianTanakaDifference_memLp hB a T),
      brownianTanakaDifferenceL2_coe B b T (brownianTanakaDifference_memLp hB b T)] with ω hd ha hc
    rw [hd, Pi.sub_apply, ha, hc, Real.norm_eq_abs]
    exact brownianTanakaDifference_level_bound B a b T ω
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity : 0 ≤ 2 * |a - b|) hb

theorem brownianTanakaDifferenceL2_level_lipschitz (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    LipschitzWith 2 (fun a => brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T)) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using
    brownianTanakaDifferenceL2_level_bound hB a b T

theorem brownianTanakaCompensation_level_continuous (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Continuous (fun a => brownianTanakaCompensation hB hBm hjoint a T) :=
  (brownianTanakaDifferenceL2_level_lipschitz hB T).continuous.sub
    (brownianSignIntegral_level_continuous hB hBm hjoint T)

theorem brownianDyadicTanakaCompensation_level_continuous (T : ℝ≥0) :
    Continuous (fun a => brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a T) :=
  brownianTanakaCompensation_level_continuous brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

end TimeTraps.Probability
