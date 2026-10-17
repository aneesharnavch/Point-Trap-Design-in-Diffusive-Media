module

public import TimeTraps.Probability.ReflectedRobinEndpointLifetimeSelectable

@[expose] public section

/-! Original medium comparison and stability now apply to independently
defined optimal actual lifetimes, with the source-normalized reaction
budget retained exactly. -/

namespace TimeTraps.Probability

open Set TimeTraps.Interval

variable {K₁ K₂ ε : ℝ}

theorem reflectedRobinEndpointLifetimeValue_mono_weight (A : EndpointArchitecture)
    (B C : IntervalMedium) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value z ≤ C.cellWeight.value z) :
    reflectedRobinEndpointLifetimeValue A B K₁ ≤ reflectedRobinEndpointLifetimeValue A C K₂ := by
  rw [reflectedRobinEndpointLifetimeValue_eq, reflectedRobinEndpointLifetimeValue_eq]
  exact A.physicalValue_mono_weight B C hK₁ hK₂ hbudget hBC

theorem reflectedRobinEndpointLifetimeValue_lt_weight (A : EndpointArchitecture)
    (B C : IntervalMedium) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value z < C.cellWeight.value z) :
    reflectedRobinEndpointLifetimeValue A B K₁ < reflectedRobinEndpointLifetimeValue A C K₂ := by
  rw [reflectedRobinEndpointLifetimeValue_eq, reflectedRobinEndpointLifetimeValue_eq]
  exact A.physicalValue_lt_weight B C hK₁ hK₂ hbudget hBC

theorem reflectedRobinEndpointLifetimeValue_stability (A : EndpointArchitecture)
    (B C : IntervalMedium) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : B.cellWeight.uniformDistance C.cellWeight ≤ ε) :
    |reflectedRobinEndpointLifetimeValue A B K₁ - reflectedRobinEndpointLifetimeValue A C K₂| ≤ ε / 2 := by
  rw [reflectedRobinEndpointLifetimeValue_eq, reflectedRobinEndpointLifetimeValue_eq]
  exact A.physicalValue_abs_sub_le_Linfty B C hK₁ hK₂ hbudget hBC

end TimeTraps.Probability
