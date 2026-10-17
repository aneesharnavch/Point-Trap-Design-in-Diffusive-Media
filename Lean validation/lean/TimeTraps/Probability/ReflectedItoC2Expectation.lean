module

public import TimeTraps.Probability.ReflectedItoRegulatorMoments

@[expose] public section

/-! Expected values in the general reflected C² Itô formula. Every term
is integrable by the proved compact-range estimates, integral isometry,
and quadratic regulator identities. The curvature term remains the
expectation of the actual ordinary time integral. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem reflectedItoC2_expected_value {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, F (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure) =
      F (reflectedFold L x) +
        D * (∫ ω, reflectedC2ItoDrift F brownianDyadicPath L D x T ω ∂brownianDyadicMeasure) +
        deriv F 0 * (∫ ω, affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) -
        deriv F L * (∫ ω, affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) := by
  have hv := (reflectedC2_value_memLp (P := brownianDyadicMeasure)
    hF brownianDyadicPath_measurable L hL D x T).integrable (by norm_num)
  have hI : Integrable (fun ω => reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T ω)
      brownianDyadicMeasure :=
    (reflectedC2ItoIntegral_memLp hF L hL D hD x T).integrable (by norm_num)
  have hd := ((reflectedC2ItoDrift_memLp (P := brownianDyadicMeasure) hF
    brownianDyadicPath_jointly_measurable L hL D x T).integrable (by norm_num)).const_mul D
  have h0 := ((reflectedLowerRegulator_memLp L hL D hD x T).integrable (by norm_num)).const_mul (deriv F 0)
  have hLr := ((reflectedUpperRegulator_memLp L hL D hD x T).integrable (by norm_num)).const_mul (deriv F L)
  have hm : (∫ ω, reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T ω
      ∂brownianDyadicMeasure) = 0 :=
    reflectedC2ItoIntegral_mean hF L hL D hD x T
  have he := integral_congr_ae (reflectedItoC2_formula hF L hL D hD x T)
  have hs := integral_sub ((hI.add hd).add h0) hLr
  have ha := integral_add (hI.add hd) h0
  have hb := integral_add hI hd
  simp only [Pi.add_apply] at hs ha hb
  rw [integral_sub hv (integrable_const _), hs, ha, hb, hm] at he
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, zero_add] at he
  linarith

end TimeTraps.Probability
