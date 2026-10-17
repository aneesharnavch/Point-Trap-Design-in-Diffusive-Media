module

public import TimeTraps.Probability.ReflectedRobinEndpointReferenceLifetime

@[expose] public section

/-! The physical lifetime is almost surely finite, and its actual real
value equals the reference clock cost before killing. Reference finiteness
has already been derived from the original endpoint equation; no finiteness premise
is added to the time-change construction. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {A : EndpointArchitecture} {K : ℝ}

theorem reflectedRobinEndpointAttainmentLifetime_ne_top {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) (x : ℝ) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetime D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p ≠ ⊤ := by
  filter_upwards [reversibleResistanceAttainmentLifetime_clock_product_ae D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength,
    reflectedRobinEndpointReferenceLifetime_ne_top hu x] with p hc hf
  rw [reflectedRobinEndpointPhysicalSite_resistance] at hc
  intro ht
  exact hf ((positiveClockLifetimeMap_eq_top_iff _ _).mp (hc.symm.trans ht))

theorem reflectedRobinEndpointAttainmentLifetimeValue_lt_top {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) (x : ℝ) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetimeValue D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p < ∞ := by
  filter_upwards [reflectedRobinEndpointAttainmentLifetime_ne_top hu x] with p hp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hp
  change nonnegativeLifetimeValue (reversibleResistanceAttainmentLifetime D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p) < ∞
  rw [← ht, nonnegativeLifetimeValue_coe]
  exact ENNReal.ofReal_lt_top

theorem reflectedRobinEndpointAttainmentLifetimeValue_cost_ae {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) (x : ℝ) :
    (fun p => (reversibleResistanceAttainmentLifetimeValue D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p).toReal)
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        reflectedRobinEndpointReferenceLifetimeCost D R x := by
  filter_upwards [reversibleResistanceAttainmentLifetime_clock_product_ae D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength,
    reflectedRobinEndpointReferenceLifetime_ne_top hu x] with p hc hf
  rw [reflectedRobinEndpointPhysicalSite_resistance] at hc
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hf
  have ht0 : 0 ≤ t := by
    have hn : (0 : WithTop ℝ) ≤ reflectedAtomicAttainmentLifetime D.medium.resistanceLength
        1 (D.medium.resistance x) (reflectedRobinEndpointReferenceData D R).site (reflectedRobinEndpointReferenceData D R).strength p :=
      attainmentKillingTime_nonneg _ _
    rw [← ht] at hn
    exact WithTop.coe_le_coe.mp hn
  have hcost : reflectedRobinEndpointReferenceLifetimeCost D R x p =
      ∫ r in (0 : ℝ)..t,
        D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1) := by
    unfold reflectedRobinEndpointReferenceLifetimeCost
    rw [← ht]
    have hs : {r : ℝ | 0 < r ∧ (r : WithTop ℝ) < (t : WithTop ℝ)} = Ioo 0 t :=
      Set.ext (fun _ => and_congr Iff.rfl WithTop.coe_lt_coe)
    rw [hs, intervalIntegral.integral_of_le ht0, integral_Ioc_eq_integral_Ioo]
  erw [← ht, positiveClockLifetimeMap_coe] at hc
  change (nonnegativeLifetimeValue
    (reversibleResistanceAttainmentLifetime D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p)).toReal = _
  rw [hc, nonnegativeLifetimeValue_coe,
    ENNReal.toReal_ofReal (reversibleResistanceClock D.medium x t.toNNReal p.1).coe_nonneg,
    reversibleResistanceClock_coe]
  calc
    _ = ∫ r in (0 : ℝ)..t,
        D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1) :=
      congrArg (fun b : ℝ => ∫ r in (0 : ℝ)..b,
        D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1))
        (Real.coe_toNNReal t ht0)
    _ = _ := hcost.symm

theorem reflectedRobinEndpointAttainmentLifetimeValue_integrable {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) (x : ℝ) :
    Integrable (fun p => (reversibleResistanceAttainmentLifetimeValue D.medium x (reflectedRobinEndpointPhysicalSite D) (reflectedRobinEndpointReferenceData D R).strength p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  (reflectedRobinEndpointReferenceLifetimeCost_integrable hu x).congr
    (reflectedRobinEndpointAttainmentLifetimeValue_cost_ae hu x).symm

end TimeTraps.Probability
