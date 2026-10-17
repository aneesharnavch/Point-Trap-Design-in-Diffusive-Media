module

public import TimeTraps.Probability.ReflectedRobinStoppingData
public import TimeTraps.Probability.ExtendedLifetimeFiniteMean

@[expose] public section

/-! Whole-time survival integrability implies finiteness of the literal
first-attainment lifetime for any finite reaction family, including
endpoint-only families. No strictly interior contact is required. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reflectedRobinCost_attainment_extended_mean (P : ReflectedRobinReactionData ι) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength
      r.toNNReal) (Ioi (0 : ℝ))) :
    (∫⁻ p, reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ENNReal.ofReal (∫ r in Ioi (0 : ℝ),
        reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) := by
  rw [reflectedAtomicAttainmentLifetimeValue_mean_survival P.length P.length_pos P.diffusivity
    P.diffusivity_pos x P.site P.strength P.strength_nonneg]
  exact (ofReal_integral_eq_lintegral_ofReal hs (Eventually.of_forall
    (fun r => (reflectedAtomicMeanSurvival_bounds P.length P.diffusivity_pos x P.site P.strength
      P.strength_nonneg r.toNNReal).1))).symm

theorem reflectedRobinCost_attainment_finite (P : ReflectedRobinReactionData ι) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength
      r.toNNReal) (Ioi (0 : ℝ))) :
    (∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p < ∞) ∧
    Integrable (fun p => (reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) ∧
    (∫ p, (reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p).toReal
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫ r in Ioi (0 : ℝ), reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal := by
  exact extendedLifetime_finite_mean (exponentialKillingMeasure brownianDyadicMeasure)
    (reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength)
    (reflectedAtomicAttainmentLifetimeValue_aemeasurable P.length P.length_pos P.diffusivity
      P.diffusivity_pos x P.site P.strength P.strength_nonneg)
    (integral_nonneg (fun r => (reflectedAtomicMeanSurvival_bounds P.length P.diffusivity_pos x P.site P.strength
      P.strength_nonneg r.toNNReal).1)) (reflectedRobinCost_attainment_extended_mean P x hs)

theorem reflectedRobinCost_attainment_ne_top (P : ReflectedRobinReactionData ι) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength
      r.toNNReal) (Ioi (0 : ℝ))) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p ≠ ⊤ := by
  filter_upwards [(reflectedRobinCost_attainment_finite P x hs).1] with p hp
  intro ht
  change nonnegativeLifetimeValue (reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p) < ∞ at hp
  rw [ht, nonnegativeLifetimeValue_top] at hp
  exact (lt_irrefl _) hp

end TimeTraps.Probability
