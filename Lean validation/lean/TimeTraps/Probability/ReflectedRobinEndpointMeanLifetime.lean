module

public import TimeTraps.Probability.ReflectedRobinEndpointLifetimeData
public import TimeTraps.Probability.ReversibleResistanceMeanLifetime

@[expose] public section

/-! The literal mean killing time for the original variable-medium
endpoint architecture solves exactly its original full-H1 equation.
Finiteness is proved, including every architecture without interior sites. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {A : EndpointArchitecture} {K : ℝ}

def reflectedRobinEndpointMeanLifetime (D : OrderedMedium A.interiorCount)
    (R : EndpointReactions A K) (x : ℝ) : ℝ :=
  reversibleResistanceMeanLifetime D.medium x (reflectedRobinEndpointPhysicalSite D)
    (reflectedRobinEndpointReferenceData D R).strength

theorem reflectedRobinEndpointMeanLifetime_eq
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    reflectedRobinEndpointMeanLifetime D R x = u x :=
  (integral_congr_ae (reflectedRobinEndpointAttainmentLifetimeValue_cost_ae hu x)).trans
    (reflectedRobinEndpointReferenceLifetimeCost_expected hu hx)

theorem reflectedRobinEndpointMeanLifetime_eqOn
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) :
    EqOn (reflectedRobinEndpointMeanLifetime D R) u (Icc D.source.left D.source.right) :=
  fun _ hx => reflectedRobinEndpointMeanLifetime_eq hu hx

theorem reflectedRobinEndpointMeanLifetime_weak_equation
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K) :
    EndpointWeakEquation D R (reflectedRobinEndpointMeanLifetime D R) := by
  obtain ⟨u, hu⟩ := endpoint_weak_state_exists D R
  exact hu.congr_state (reflectedRobinEndpointMeanLifetime_eqOn hu).symm

theorem reflectedRobinEndpointMeanLifetime_finite
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K) (x : ℝ) :
    (∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetimeValue D.medium x (reflectedRobinEndpointPhysicalSite D)
        (reflectedRobinEndpointReferenceData D R).strength p < ∞) ∧
    Integrable (fun p => (reversibleResistanceAttainmentLifetimeValue D.medium x
      (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  ⟨reflectedRobinEndpointAttainmentLifetimeValue_lt_top
      (reflectedRobinEndpointMeanLifetime_weak_equation D R) x,
    reflectedRobinEndpointAttainmentLifetimeValue_integrable
      (reflectedRobinEndpointMeanLifetime_weak_equation D R) x⟩

theorem reflectedRobinEndpointMeanLifetime_value_aemeasurable
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K) (x : ℝ) :
    AEMeasurable (reversibleResistanceAttainmentLifetimeValue D.medium x
      (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength)
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  apply (reflectedRobinEndpointMeanLifetime_finite D R x).2.aestronglyMeasurable.aemeasurable.ennreal_ofReal.congr
  filter_upwards [(reflectedRobinEndpointMeanLifetime_finite D R x).1] with p hp
  exact ENNReal.ofReal_toReal hp.ne

theorem reflectedRobinEndpointMeanLifetime_extended_mean
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K) (x : ℝ) :
    (∫⁻ p, reversibleResistanceAttainmentLifetimeValue D.medium x
      (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ENNReal.ofReal (reflectedRobinEndpointMeanLifetime D R x) := by
  calc
    _ = ∫⁻ p, ENNReal.ofReal ((reversibleResistanceAttainmentLifetimeValue D.medium x
        (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p).toReal)
        ∂exponentialKillingMeasure brownianDyadicMeasure := by
      apply lintegral_congr_ae
      filter_upwards [(reflectedRobinEndpointMeanLifetime_finite D R x).1] with p hp
      exact (ENNReal.ofReal_toReal hp.ne).symm
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      (reflectedRobinEndpointMeanLifetime_finite D R x).2
      (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))).symm

theorem reflectedRobinEndpointMeanLifetime_positive
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K)
    {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    0 < reflectedRobinEndpointMeanLifetime D R x :=
  (reflectedRobinEndpointMeanLifetime_weak_equation D R).positive x hx

end TimeTraps.Probability

end
