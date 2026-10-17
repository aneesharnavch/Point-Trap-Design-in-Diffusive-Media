module

public import TimeTraps.Probability.ReflectedC2ItoIntegrand
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! The physical isometry and zero mean of the actual original-Brownian
integral for an arbitrary globally C² reflected test. Only its derivative
on the compact interval is bounded; no endpoint condition is imposed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedC2Ito_slope_square_integrable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2)
      (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  have ht : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    (by fun_prop : Measurable (fun p : ℝ × (ℕ → ℝ) => p.1.toNNReal)).prodMk measurable_snd
  have hB := brownianDyadicPath_jointly_measurable.comp ht
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2) :=
    ((reflectedFellerExtension L hL (reflectedC2DerivativeMap hF L)).continuous.measurable.comp
      (measurable_const.add (measurable_const.mul hB))).pow_const 2
  apply (integrable_const (‖(reflectedC2DerivativeMap hF L)‖ ^ 2)).mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  have hb : |deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)| ≤
      ‖(reflectedC2DerivativeMap hF L)‖ :=
    reflectedFellerExtension_bound L hL (reflectedC2DerivativeMap hF L)
      (x + Real.sqrt (2 * D) * brownianDyadicPath p.1.toNNReal p.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
    abs_nonneg (deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
    norm_nonneg (reflectedC2DerivativeMap hF L)]

theorem reflectedC2ItoIntegrand_square_coe {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (fun p => (reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) p ^ 2)
      =ᵐ[volume.prod brownianDyadicMeasure]
    ((Ioc (0 : ℝ) T.val) ×ˢ (univ : Set (ℕ → ℝ))).indicator
      (fun p => 2 * D * deriv F
        (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [reflectedC2ItoIntegrand_coe hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T,
    brownianDyadicFoldSlope_square_prod_ae L hL x hσ T] with p hp hunit
  unfold brownianSquareProcess at hp
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hpt : p ∈ (Ioc (0 : ℝ) T.val) ×ˢ (univ : Set (ℕ → ℝ)) := ⟨ht, mem_univ _⟩
    rw [hp, Set.indicator_of_mem ht, one_mul, Set.indicator_of_mem hpt,
      mul_pow, mul_pow, hunit ht, mul_one, Real.sq_sqrt (by positivity)]
  · have hpt : p ∉ (Ioc (0 : ℝ) T.val) ×ˢ (univ : Set (ℕ → ℝ)) := fun h => ht h.1
    rw [hp, Set.indicator_of_notMem ht, zero_mul, zero_pow (by norm_num),
      Set.indicator_of_notMem hpt]

theorem reflectedC2ItoIntegral_isometry {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianStochasticIntegral (reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T) ω ^ 2
      ∂brownianDyadicMeasure) =
    2 * D * ∫ p : ℝ × (ℕ → ℝ),
      deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
      ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  rw [brownianStochasticIntegral_isometry,
    integral_congr_ae (reflectedC2ItoIntegrand_square_coe hF L hL D hD x T),
    integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ),
    ← Measure.prod_restrict, Measure.restrict_univ, integral_const_mul]

theorem reflectedC2ItoIntegral_memLp {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    MemLp (brownianStochasticIntegral (reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T)) 2
      brownianDyadicMeasure :=
  Lp.memLp _

theorem reflectedC2ItoIntegral_mean {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianStochasticIntegral (reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T) ω
      ∂brownianDyadicMeasure) = 0 :=
  brownianStochasticIntegral_mean _

end TimeTraps.Probability
