module

public import TimeTraps.Probability.ReflectedRobinEndpointLifetimeOptimization
public import TimeTraps.Interval.EndpointSelectable

@[expose] public section

/-! Choosing an endpoint architecture minimizes the actual lifetime
over the tagged union of the original physical design spaces. Both
branches retain all designs, including zero interior-site designs. -/

noncomputable section

namespace TimeTraps.Probability

open Set TimeTraps.Interval

variable {A₁ A₂ : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

def reflectedRobinEndpointLifetimeValue (A : EndpointArchitecture) (B : IntervalMedium) (K : ℝ) : ℝ :=
  sInf (range (fun E : EndpointPhysicalDesign A B K => reflectedRobinEndpointLifetimeWorst E))

def reflectedRobinEndpointAlternativeWorst (E : EndpointAlternative A₁ A₂ B K) : ℝ :=
  E.elim reflectedRobinEndpointLifetimeWorst reflectedRobinEndpointLifetimeWorst

theorem reflectedRobinEndpointLifetimeValue_eq (A : EndpointArchitecture) (B : IntervalMedium) (K : ℝ) :
    reflectedRobinEndpointLifetimeValue A B K = A.physicalValue B K := by
  unfold reflectedRobinEndpointLifetimeValue EndpointArchitecture.physicalValue
  rw [reflectedRobinEndpointLifetimeWorst_values_eq]

theorem reflectedRobinEndpointAlternativeWorst_eq (E : EndpointAlternative A₁ A₂ B K) :
    reflectedRobinEndpointAlternativeWorst E = E.cost := by
  cases E <;> exact reflectedRobinEndpointLifetimeWorst_eq _

theorem reflectedRobinEndpointAlternative_minimum
    (A₁ A₂ : EndpointArchitecture) (B : IntervalMedium) (hK : 0 < K) :
    IsLeast (range (fun E : EndpointAlternative A₁ A₂ B K => reflectedRobinEndpointAlternativeWorst E))
      (min (reflectedRobinEndpointLifetimeValue A₁ B K) (reflectedRobinEndpointLifetimeValue A₂ B K)) := by
  simp only [reflectedRobinEndpointAlternativeWorst_eq, reflectedRobinEndpointLifetimeValue_eq]
  exact endpoint_alternative_minimum A₁ A₂ B hK

theorem reflectedRobinEndpointAlternative_optimal_iff
    (E : EndpointAlternative A₁ A₂ B K) (hK : 0 < K) :
    (∀ F : EndpointAlternative A₁ A₂ B K,
      reflectedRobinEndpointAlternativeWorst E ≤ reflectedRobinEndpointAlternativeWorst F) ↔
    reflectedRobinEndpointAlternativeWorst E =
      min (reflectedRobinEndpointLifetimeValue A₁ B K) (reflectedRobinEndpointLifetimeValue A₂ B K) := by
  simp only [reflectedRobinEndpointAlternativeWorst_eq, reflectedRobinEndpointLifetimeValue_eq]
  exact E.optimal_iff_cost_eq hK

theorem reflectedRobinEndpointAlternative_left_optimal_iff
    (E : EndpointPhysicalDesign A₁ B K) :
    (∀ F : EndpointAlternative A₁ A₂ B K,
      reflectedRobinEndpointAlternativeWorst (Sum.inl E : EndpointAlternative A₁ A₂ B K) ≤ reflectedRobinEndpointAlternativeWorst F) ↔
      (∀ F : EndpointPhysicalDesign A₁ B K,
        reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) ∧
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeValue A₂ B K := by
  simp only [reflectedRobinEndpointAlternativeWorst_eq, reflectedRobinEndpointLifetimeWorst_eq,
    reflectedRobinEndpointLifetimeValue_eq]
  exact endpoint_alternative_left_optimal_iff E

theorem reflectedRobinEndpointAlternative_right_optimal_iff
    (E : EndpointPhysicalDesign A₂ B K) :
    (∀ F : EndpointAlternative A₁ A₂ B K,
      reflectedRobinEndpointAlternativeWorst (Sum.inr E : EndpointAlternative A₁ A₂ B K) ≤ reflectedRobinEndpointAlternativeWorst F) ↔
      (∀ F : EndpointPhysicalDesign A₂ B K,
        reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) ∧
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeValue A₁ B K := by
  simp only [reflectedRobinEndpointAlternativeWorst_eq, reflectedRobinEndpointLifetimeWorst_eq,
    reflectedRobinEndpointLifetimeValue_eq]
  exact endpoint_alternative_right_optimal_iff E

end TimeTraps.Probability

end
