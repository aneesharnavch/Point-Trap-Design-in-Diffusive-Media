module

public import TimeTraps.Probability.ReflectedRobinEndpointReferenceData
public import TimeTraps.Probability.ReversibleResistanceTimeChangeAtomicHazard

@[expose] public section

/-! The actual physical endpoint hazard is exactly the reference Robin
hazard at the inverse physical clock. Thus endpoint strengths remain
unchanged and multiply the actual boundary regulators of unit diffusion. -/

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

variable {A : EndpointArchitecture} {K : ℝ}

theorem reflectedRobinEndpointHazard_reference
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K)
    (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceAtomicHazard D.medium x (reflectedRobinEndpointPhysicalSite D)
      (reflectedRobinEndpointReferenceData D R).strength T ω =
      reflectedRobinHazard D.medium.resistanceLength 1 (D.medium.resistance x)
        (fun i => D.medium.resistance (D.site i)) R.interiorStrength R.leftStrength R.rightStrength
        (reversibleResistanceInversePath D.medium x T ω) ω := by
  rw [reversibleResistanceAtomicHazard_reference, reflectedRobinEndpointPhysicalSite_resistance,
    reflectedRobinHazard_eq_atomic _ zero_lt_one]
  rfl

theorem reflectedRobinEndpointSurvival_reference
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K)
    (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceAtomicSurvival D.medium x (reflectedRobinEndpointPhysicalSite D)
      (reflectedRobinEndpointReferenceData D R).strength T ω =
      reflectedRobinSurvival D.medium.resistanceLength 1 (D.medium.resistance x)
        (fun i => D.medium.resistance (D.site i)) R.interiorStrength R.leftStrength R.rightStrength
        (reversibleResistanceInversePath D.medium x T ω) ω := by
  rw [reversibleResistanceAtomicSurvival, reflectedRobinSurvival, reflectedRobinEndpointHazard_reference]

theorem reflectedRobinEndpointHazard_regulators
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K)
    (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceAtomicHazard D.medium x (reflectedRobinEndpointPhysicalSite D)
      (reflectedRobinEndpointReferenceData D R).strength T ω =
      reflectedAtomicHazard D.medium.resistanceLength 1 (D.medium.resistance x)
        (fun i => D.medium.resistance (D.site i)) R.interiorStrength
        (reversibleResistanceInversePath D.medium x T ω) ω +
      R.leftStrength * affineBrownianLowerRegulator (D.medium.resistance x) (Real.sqrt 2)
        D.medium.resistanceLength (reversibleResistanceInversePath D.medium x T ω) ω +
      R.rightStrength * affineBrownianUpperRegulator (D.medium.resistance x) (Real.sqrt 2)
        D.medium.resistanceLength (reversibleResistanceInversePath D.medium x T ω) ω := by
  rw [reflectedRobinEndpointHazard_reference, reflectedRobinHazard]
  simp only [div_one, mul_one]

end TimeTraps.Probability
