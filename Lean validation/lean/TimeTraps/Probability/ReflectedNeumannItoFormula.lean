module

public import TimeTraps.Probability.ReflectedNeumannItoIntegrand
public import TimeTraps.Probability.ReflectedNeumannDynkinProcess

@[expose] public section

/-! The C² Neumann Itô formula for the actual folded Brownian trajectory.
The martingale term is the actual closed stochastic integral of the
physical slope times the fold sign and sqrt(2D). The formula holds on
one almost-sure event for every time in a fixed compact interval. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedNeumannIto_continuous_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      F.value (foldedTrajectory L D x brownianDyadicPath t ω) -
        F.value (reflectedFold L x) = reflectedNeumannItoIntegralPath F hL D x T t ω +
        D * ∫ r in (0 : ℝ)..t.val,
          F.curvature (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) := by
  filter_upwards [brownianDiffusionItoTanakaC2_continuous_ae
    (F.extension_global_contDiff hL) (M₂ := ‖F.curvatureMap‖₊)
    (F.extension_global_second_bound hL) (∅ : Finset Unit)
    (fun _ => 0) (fun _ => 0) x hD T] with ω he
  intro t ht
  have hd : brownianItoDrift (affineBrownianInput x (Real.sqrt (2 * D)))
      (deriv (deriv (reflectedFellerExtension L hL F.valueMap))) t ω =
      ∫ r in (0 : ℝ)..t.val,
        F.curvature (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) := by
    unfold brownianItoDrift
    congr 1
    funext r
    exact F.extension_global_second hL _
  have hh := he t ht
  simp only [finiteKinkPotential, Finset.sum_empty, add_zero, mul_zero] at hh
  rw [hd] at hh
  exact hh

theorem reflectedNeumannIto_physical_continuous_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (hx : x ∈ Icc 0 L) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      F.value (foldedTrajectory L D x brownianDyadicPath t ω) - F.value x =
        reflectedNeumannItoIntegralPath F hL D x T t ω +
        D * ∫ r in (0 : ℝ)..t.val,
          F.curvature (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) := by
  simpa only [reflectedFold_eq_self L hL x hx] using
    reflectedNeumannIto_continuous_ae F hL D hD x T

theorem reflectedNeumannDynkin_eq_ito_continuous_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      reflectedNeumannDynkin F hL brownianDyadicPath D x t ω =
        reflectedNeumannItoIntegralPath F hL D x T t ω := by
  filter_upwards [reflectedNeumannIto_continuous_ae F hL D hD x T,
    brownianDyadicPath_start_zero] with ω he hzero
  intro t ht
  rw [reflectedNeumannDynkin_physical]
  have hi : foldedTrajectory L D x brownianDyadicPath 0 ω = reflectedFold L x := by
    simp only [foldedTrajectory, hzero, mul_zero, add_zero]
  rw [hi, he t ht]
  ring

theorem reflectedNeumannDynkin_eq_stochasticIntegral_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    reflectedNeumannDynkin F hL brownianDyadicPath D x T =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T) := by
  filter_upwards [reflectedNeumannDynkin_eq_ito_continuous_ae F hL D hD x T,
    reflectedNeumannItoIntegralPath_integral_ae F hL D x T T] with ω he hi
  rw [he T le_rfl, hi]
  change brownianStochasticIntegral
    (brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure T
      (reflectedNeumannItoIntegrand F hL D x T)) ω = _
  rw [reflectedNeumannItoIntegrand_cutoff, min_self]

end TimeTraps.Probability
