module

public import TimeTraps.Probability.ReflectedItoC2Formula
public import TimeTraps.Probability.ReflectedItoBoundaryQuadratic
public import TimeTraps.Probability.ReflectedC2ItoIsometry

@[expose] public section

/-! Actual regulator moments from the two quadratic reflected Itô tests.
The regulators are the established lattice sums. Square integrability
and exact means are derived from their stochastic-integral identities. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem reflectedUpperRegulator_quadratic_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T =ᵐ[brownianDyadicMeasure]
      (fun ω => reflectedC2ItoIntegral (reflectedUpperBoundaryTest_contDiff L)
        brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL D hD x T ω + D * T.val / L -
        (reflectedUpperBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) -
          reflectedUpperBoundaryTest L (reflectedFold L x))) := by
  filter_upwards [reflectedItoC2_formula (reflectedUpperBoundaryTest_contDiff L)
    L hL D hD x T] with ω h
  simp only [reflectedUpperBoundaryTest_deriv L hL, zero_div, div_self (ne_of_gt hL),
    zero_mul, one_mul, add_zero, reflectedUpperBoundaryTest_drift brownianDyadicPath L hL D x T ω] at h
  linear_combination h

theorem reflectedLowerRegulator_quadratic_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T =ᵐ[brownianDyadicMeasure]
      (fun ω => (reflectedLowerBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) -
          reflectedLowerBoundaryTest L (reflectedFold L x)) -
        reflectedC2ItoIntegral (reflectedLowerBoundaryTest_contDiff L)
          brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
          brownianDyadicPath_jointly_measurable L hL D hD x T ω + D * T.val / L) := by
  filter_upwards [reflectedItoC2_formula (reflectedLowerBoundaryTest_contDiff L)
    L hL D hD x T] with ω h
  simp only [reflectedLowerBoundaryTest_deriv L hL, zero_div, sub_zero,
    div_self (ne_of_gt hL), sub_self, zero_mul, one_mul,
    reflectedLowerBoundaryTest_drift brownianDyadicPath L hL D x T ω] at h
  linear_combination -h

theorem reflectedUpperRegulator_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    MemLp (affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T) 2 brownianDyadicMeasure := by
  have hI := reflectedC2ItoIntegral_memLp (reflectedUpperBoundaryTest_contDiff L) L hL D hD x T
  have hv := reflectedC2_value_difference_memLp (P := brownianDyadicMeasure)
    (reflectedUpperBoundaryTest_contDiff L) brownianDyadicPath_measurable L hL D x T
  exact (((hI.add (memLp_const (D * T.val / L))).sub hv).ae_eq
    (reflectedUpperRegulator_quadratic_ae L hL D hD x T).symm)

theorem reflectedLowerRegulator_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    MemLp (affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T) 2 brownianDyadicMeasure := by
  have hI := reflectedC2ItoIntegral_memLp (reflectedLowerBoundaryTest_contDiff L) L hL D hD x T
  have hv := reflectedC2_value_difference_memLp (P := brownianDyadicMeasure)
    (reflectedLowerBoundaryTest_contDiff L) brownianDyadicPath_measurable L hL D x T
  exact (((hv.sub hI).add (memLp_const (D * T.val / L))).ae_eq
    (reflectedLowerRegulator_quadratic_ae L hL D hD x T).symm)

theorem reflectedUpperRegulator_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) =
      D * T.val / L - ∫ ω,
        (reflectedUpperBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) -
          reflectedUpperBoundaryTest L (reflectedFold L x)) ∂brownianDyadicMeasure := by
  let I : (ℕ → ℝ) → ℝ := fun ω => reflectedC2ItoIntegral (reflectedUpperBoundaryTest_contDiff L)
    brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL D hD x T ω
  let V : (ℕ → ℝ) → ℝ := fun ω =>
    reflectedUpperBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) -
      reflectedUpperBoundaryTest L (reflectedFold L x)
  let c : ℝ := D * T.val / L
  have hI : Integrable I brownianDyadicMeasure :=
    (reflectedC2ItoIntegral_memLp (reflectedUpperBoundaryTest_contDiff L) L hL D hD x T).integrable (by norm_num)
  have hv : Integrable V brownianDyadicMeasure :=
    (reflectedC2_value_difference_memLp (P := brownianDyadicMeasure)
      (reflectedUpperBoundaryTest_contDiff L) brownianDyadicPath_measurable L hL D x T).integrable (by norm_num)
  have hc : Integrable (fun _ : ℕ → ℝ => c) brownianDyadicMeasure := integrable_const c
  have hm : (∫ ω, I ω ∂brownianDyadicMeasure) = 0 :=
    reflectedC2ItoIntegral_mean (reflectedUpperBoundaryTest_contDiff L) L hL D hD x T
  change _ = c - ∫ ω, V ω ∂brownianDyadicMeasure
  calc
    _ = ∫ ω, I ω + c - V ω ∂brownianDyadicMeasure :=
      integral_congr_ae (reflectedUpperRegulator_quadratic_ae L hL D hD x T)
    _ = ((∫ ω, I ω ∂brownianDyadicMeasure) + (∫ _ : ℕ → ℝ, c ∂brownianDyadicMeasure)) -
        ∫ ω, V ω ∂brownianDyadicMeasure :=
      (integral_sub (hI.add hc) hv).trans
        (congrArg (fun z => z - ∫ ω, V ω ∂brownianDyadicMeasure) (integral_add hI hc))
    _ = _ := by
      rw [hm]
      simp only [integral_const, probReal_univ, one_smul, zero_add]

theorem reflectedLowerRegulator_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) =
      (∫ ω, (reflectedLowerBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) -
          reflectedLowerBoundaryTest L (reflectedFold L x)) ∂brownianDyadicMeasure) + D * T.val / L := by
  let I : (ℕ → ℝ) → ℝ := fun ω => reflectedC2ItoIntegral (reflectedLowerBoundaryTest_contDiff L)
    brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL D hD x T ω
  let V : (ℕ → ℝ) → ℝ := fun ω =>
    reflectedLowerBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) -
      reflectedLowerBoundaryTest L (reflectedFold L x)
  let c : ℝ := D * T.val / L
  have hI : Integrable I brownianDyadicMeasure :=
    (reflectedC2ItoIntegral_memLp (reflectedLowerBoundaryTest_contDiff L) L hL D hD x T).integrable (by norm_num)
  have hv : Integrable V brownianDyadicMeasure :=
    (reflectedC2_value_difference_memLp (P := brownianDyadicMeasure)
      (reflectedLowerBoundaryTest_contDiff L) brownianDyadicPath_measurable L hL D x T).integrable (by norm_num)
  have hc : Integrable (fun _ : ℕ → ℝ => c) brownianDyadicMeasure := integrable_const c
  have hm : (∫ ω, I ω ∂brownianDyadicMeasure) = 0 :=
    reflectedC2ItoIntegral_mean (reflectedLowerBoundaryTest_contDiff L) L hL D hD x T
  change _ = (∫ ω, V ω ∂brownianDyadicMeasure) + c
  calc
    _ = ∫ ω, V ω - I ω + c ∂brownianDyadicMeasure :=
      integral_congr_ae (reflectedLowerRegulator_quadratic_ae L hL D hD x T)
    _ = ((∫ ω, V ω ∂brownianDyadicMeasure) - (∫ ω, I ω ∂brownianDyadicMeasure)) +
        ∫ _ : ℕ → ℝ, c ∂brownianDyadicMeasure :=
      (integral_add (hv.sub hI) hc).trans
        (congrArg (fun z => z + ∫ _ : ℕ → ℝ, c ∂brownianDyadicMeasure) (integral_sub hv hI))
    _ = _ := by
      rw [hm]
      simp only [integral_const, probReal_univ, one_smul, sub_zero]

end TimeTraps.Probability
