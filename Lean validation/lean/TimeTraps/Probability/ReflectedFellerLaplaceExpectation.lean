module

public import TimeTraps.Probability.ReflectedFellerLaplacePayoff

@[expose] public section

/-! The infinite-horizon expectation identity at every deterministic
starting point of the actual folded Brownian path. Its one-time laws and
the proved product integrability justify the marginal substitution and
Fubini; no killing functional or point-contact interaction is introduced. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set

theorem reflectedDiscountedPayoff_mean (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (α : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) (t : ℝ) :
    (∫ ω, reflectedDiscountedPayoff L hL D α f x.val t ω ∂brownianDyadicMeasure) =
      Real.exp (-α * t) * reflectedFellerTimeOperator L hL D t f x := by
  unfold reflectedDiscountedPayoff
  rw [integral_const_mul]
  congr 1
  have he := (foldedTrajectory_gaussian_hasLaw brownianDyadicPath_isPreBrownianReal
    L D hD x.val t.toNNReal).integral_comp
      (reflectedFellerExtension L hL f).continuous.aestronglyMeasurable
  rw [reflectedFellerTimeOperator, reflectedFellerOperator_kernel]
  rw [Real.toNNReal_mul (show 0 ≤ 2 * D by positivity)]
  exact he

theorem reflectedFellerLaplace_expectation (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) :
    reflectedFellerLaplace L hL D α f x =
      ∫ ω, (∫ t in Ioi (0 : ℝ), reflectedDiscountedPayoff L hL D α f x.val t ω)
        ∂brownianDyadicMeasure := by
  rw [← integral_integral_swap (reflectedDiscountedPayoff_joint_integrable L hL D hα f x.val)]
  rw [reflectedFellerLaplace_apply L hL D hα f x]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => (reflectedDiscountedPayoff_mean L hL D hD α f x t).symm)

theorem reflectedFellerLaplace_expectation_path (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) :
    reflectedFellerLaplace L hL D α f x =
      ∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
        f ⟨foldedTrajectory L D x.val brownianDyadicPath t.toNNReal ω,
          foldedTrajectory_mem L hL D x.val brownianDyadicPath t.toNNReal ω⟩)
        ∂brownianDyadicMeasure := by
  rw [reflectedFellerLaplace_expectation L hL D hD hα f x]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  unfold reflectedDiscountedPayoff
  rw [reflectedFellerExtension_on_interval L hL f
    ⟨_, foldedTrajectory_mem L hL D x.val brownianDyadicPath t.toNNReal ω⟩]

end TimeTraps.Probability
