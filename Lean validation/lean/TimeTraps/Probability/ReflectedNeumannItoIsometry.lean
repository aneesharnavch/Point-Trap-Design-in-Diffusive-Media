module

public import TimeTraps.Probability.ReflectedNeumannItoIntegrand
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! The exact energy and mean of the original Brownian stochastic integral
for a reflected C2 Neumann test. The fold sign has square one in positive
time product measure, giving the physical coefficient 2D without any
stochastic associativity assertion involving the derived reflected driver. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedNeumannIto_slope_square_integrable {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2)
      (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  have ht : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    (by fun_prop : Measurable (fun p : ℝ × (ℕ → ℝ) => p.1.toNNReal)).prodMk measurable_snd
  have hB := brownianDyadicPath_jointly_measurable.comp ht
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2) :=
    ((reflectedFellerExtension L hL F.slopeMap).continuous.measurable.comp
      (measurable_const.add (measurable_const.mul hB))).pow_const 2
  apply (integrable_const (‖F.slopeMap‖ ^ 2)).mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  have hb : |F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)| ≤
      ‖F.slopeMap‖ :=
    reflectedFellerExtension_bound L hL F.slopeMap
      (x + Real.sqrt (2 * D) * brownianDyadicPath p.1.toNNReal p.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
    abs_nonneg (F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
    norm_nonneg F.slopeMap]

theorem reflectedNeumannItoIntegrand_square_coe {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (fun p => (reflectedNeumannItoIntegrand F hL D x T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) p ^ 2)
      =ᵐ[volume.prod brownianDyadicMeasure]
    ((Ioc (0 : ℝ) T.val) ×ˢ (univ : Set (ℕ → ℝ))).indicator
      (fun p => 2 * D * F.slope
        (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [reflectedNeumannItoIntegrand_coe F hL D hD x T,
    brownianDyadicFoldSlope_square_prod_ae L hL x hσ T] with p hp hunit
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hpt : p ∈ (Ioc (0 : ℝ) T.val) ×ˢ (univ : Set (ℕ → ℝ)) := ⟨ht, mem_univ _⟩
    rw [hp, Set.indicator_of_mem ht, one_mul, Set.indicator_of_mem hpt,
      mul_pow, mul_pow, hunit ht, mul_one, Real.sq_sqrt (by positivity)]
  · have hpt : p ∉ (Ioc (0 : ℝ) T.val) ×ˢ (univ : Set (ℕ → ℝ)) := fun h => ht h.1
    rw [hp, Set.indicator_of_notMem ht, zero_mul, zero_pow (by norm_num),
      Set.indicator_of_notMem hpt]

theorem reflectedNeumannItoIntegral_isometry {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T) ω ^ 2
      ∂brownianDyadicMeasure) =
    2 * D * ∫ p : ℝ × (ℕ → ℝ),
      F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
      ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  rw [brownianStochasticIntegral_isometry,
    integral_congr_ae (reflectedNeumannItoIntegrand_square_coe F hL D hD x T),
    integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ),
    ← Measure.prod_restrict, Measure.restrict_univ, integral_const_mul]

theorem reflectedNeumannItoIntegral_memLp {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    MemLp (brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T)) 2
      brownianDyadicMeasure :=
  Lp.memLp _

theorem reflectedNeumannItoIntegral_mean {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T) ω
      ∂brownianDyadicMeasure) = 0 :=
  brownianStochasticIntegral_mean _

end TimeTraps.Probability
