module

public import TimeTraps.Probability.ReflectedRobinEndpointReferenceData
public import TimeTraps.Probability.ReflectedRobinStopping
public import TimeTraps.Probability.ReflectedRobinStoppingLifetime
public import TimeTraps.Probability.ReversibleResistanceLifetimeTimeChange

@[expose] public section

/-! The original endpoint equation proves integrability of the actual
clock accumulated before reference killing. This includes left-only,
right-only and both-endpoint architectures with no interior trap. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {A : EndpointArchitecture} {K : ℝ}

def reflectedRobinEndpointReferenceLifetimeCost (D : OrderedMedium A.interiorCount)
    (R : EndpointReactions A K) (x : ℝ) (p : (ℕ → ℝ) × ℝ) : ℝ :=
  ∫ r in {r : ℝ | 0 < r ∧ (r : WithTop ℝ) <
    reflectedAtomicAttainmentLifetime D.medium.resistanceLength 1 (D.medium.resistance x)
      (reflectedRobinEndpointReferenceData D R).site (reflectedRobinEndpointReferenceData D R).strength p},
    D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1)

theorem reflectedRobinEndpointReferenceLifetime_ne_top
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) (x : ℝ) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetime D.medium.resistanceLength 1 (D.medium.resistance x)
        (reflectedRobinEndpointReferenceData D R).site (reflectedRobinEndpointReferenceData D R).strength p ≠ ⊤ :=
  reflectedRobinCost_attainment_ne_top (reflectedRobinEndpointReferenceData D R) (D.medium.resistance x)
    (reflectedRobinEndpoint_survival_integrable hu (D.medium.resistance x))

theorem reflectedRobinEndpointReferenceLifetimeCost_integrable
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) (x : ℝ) :
    Integrable (reflectedRobinEndpointReferenceLifetimeCost D R x)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  reflectedRobinCostStoppedValue_path_cost_integrable
    (P := reflectedRobinEndpointReferenceData D R)
    D.medium.resistanceSpeed_continuous.continuousOn (D.medium.resistance x)
    (reflectedRobinEndpoint_survival_integrable hu (D.medium.resistance x))

theorem reflectedRobinEndpointReferenceLifetimeCost_expected
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    (∫ p, reflectedRobinEndpointReferenceLifetimeCost D R x p
      ∂exponentialKillingMeasure brownianDyadicMeasure) = u x :=
  (reflectedRobinCostStoppedValue_expected_infinite (P := reflectedRobinEndpointReferenceData D R)
    D.medium.resistanceSpeed_continuous.continuousOn (D.medium.resistance x)
    (reflectedRobinEndpoint_survival_integrable hu (D.medium.resistance x))).trans
    (reflectedRobinEndpoint_cost_expectation hu hx)

end TimeTraps.Probability

end
