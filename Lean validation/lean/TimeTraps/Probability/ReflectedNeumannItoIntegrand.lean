module

public import TimeTraps.Probability.ReflectedNeumannC2Extension
public import TimeTraps.Probability.ReflectedNeumannItoSlope
public import TimeTraps.Probability.BrownianAffineItoTanakaC2Mean
public import TimeTraps.Probability.ReflectedFoldTrajectory

@[expose] public section

/-! The actual closed stochastic integrand of a C2 Neumann test along
the reflected trajectory. Its coefficient is the physical slope times
the fold sign and sqrt(2D), in the original Brownian integral space. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedNeumannItoIntegrand {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  brownianAffineFiniteKinkC2Integrand (F.extension_global_contDiff hL)
    (M₂ := ‖F.curvatureMap‖₊) (F.extension_global_second_bound hL)
    (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) x (Real.sqrt (2 * D)) T

theorem reflectedNeumannItoIntegrand_coe {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (reflectedNeumannItoIntegrand F hL D x T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        (Real.sqrt (2 * D) * (F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) *
          reflectedFoldSlope L (x + Real.sqrt (2 * D) * brownianDyadicPath p.1.toNNReal p.2)))) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hr : (reflectedNeumannItoIntegrand F hL D x T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        (Real.sqrt (2 * D) * deriv (reflectedFellerExtension L hL F.valueMap)
          (affineBrownianInput x (Real.sqrt (2 * D)) p.1.toNNReal p.2))) := by
    simpa only [reflectedNeumannItoIntegrand, finiteKinkSlope, Finset.sum_empty, add_zero] using
      brownianAffineFiniteKinkC2Integrand_coe (F.extension_global_contDiff hL)
        (M₂ := ‖F.curvatureMap‖₊) (F.extension_global_second_bound hL)
        (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) x hσ T
  refine hr.trans ?_
  filter_upwards [F.extension_fold_deriv_prod_ae hL brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_jointly_measurable x hσ T] with p hp
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
  · simp only [Set.indicator_of_mem ht, one_mul]
    exact congrArg (fun z => Real.sqrt (2 * D) * z) (hp ht)
  · simp only [Set.indicator_of_notMem ht, zero_mul]

theorem reflectedNeumannItoIntegrand_cutoff {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T t : ℝ≥0) :
    brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure t
      (reflectedNeumannItoIntegrand F hL D x T) = reflectedNeumannItoIntegrand F hL D x (min t T) := by
  simp only [reflectedNeumannItoIntegrand, brownianAffineFiniteKinkC2Integrand,
    brownianFiniteKinkC2Integrand, Finset.sum_empty, add_zero]
  exact brownianLipschitzIntegrand_cutoff brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable _ brownianDyadicPath_jointly_measurable T t

noncomputable def reflectedNeumannItoIntegralPath {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) : ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath (reflectedNeumannItoIntegrand F hL D x T)

theorem reflectedNeumannItoIntegralPath_integral_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T t : ℝ≥0) :
    reflectedNeumannItoIntegralPath F hL D x T t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralUpTo t (reflectedNeumannItoIntegrand F hL D x T) :=
  brownianIntegralGlobalPath_integral_ae _ t

theorem reflectedNeumannItoIntegralPath_continuous {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => reflectedNeumannItoIntegralPath F hL D x T t ω) :=
  brownianIntegralGlobalPath_continuous _ ω

end TimeTraps.Probability
