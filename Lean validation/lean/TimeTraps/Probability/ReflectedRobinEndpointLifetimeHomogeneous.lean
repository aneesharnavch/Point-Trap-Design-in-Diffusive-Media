module

public import TimeTraps.Probability.ReflectedRobinEndpointLifetimeOptimization
public import TimeTraps.Interval.EndpointHomogeneousCorollaries

@[expose] public section

/-! The physical expected-lifetime objective satisfies the explicit
2m+b law, with every equality case characterized by the same original
sites and endpoint/interior strengths. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis TimeTraps.Interval

variable (A : EndpointArchitecture) {L D K : ℝ}

theorem reflectedRobinEndpointLifetime_homogeneous_minimum
    (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    IsLeast (range (fun E : EndpointPhysicalDesign A (homogeneous L D hL hD) K =>
      reflectedRobinEndpointLifetimeWorst E)) (L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2)) := by
  rw [reflectedRobinEndpointLifetimeWorst_values_eq]
  exact endpoint_homogeneous_minimum A hL hD hK

theorem reflectedRobinEndpointLifetime_two_m_plus_b_minimum
    (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    IsLeast (range (fun E : EndpointPhysicalDesign A (homogeneous L D hL hD) K =>
      reflectedRobinEndpointLifetimeWorst E))
      (L / K + L ^ 2 /
        (2 * D * (2 * (A.interiorCount : ℝ) + A.leftReactive.toNat + A.rightReactive.toNat) ^ 2)) := by
  rw [reflectedRobinEndpointLifetimeWorst_values_eq]
  exact endpoint_homogeneous_two_m_plus_b_minimum A hL hD hK

theorem reflectedRobinEndpointLifetime_homogeneous_optimizer_iff
    (hL : 0 < L) (hD : 0 < D) (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) :
    (∀ F : EndpointPhysicalDesign A (homogeneous L D hL hD) K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) ↔
      (∀ j, E.geometry.site j = L * ((A.leftReactive.toNat : ℝ) + 2 * (j.val : ℝ) + 1) / A.sideTotal) ∧
      (∀ i, E.reactions.activeStrength i = K * A.homogeneousShare i) :=
  (reflectedRobinEndpointLifetimeWorst_optimal_iff E).trans (endpoint_homogeneous_optimal_iff A hL hD E)

theorem reflectedRobinEndpointLifetime_homogeneous_equality_iff
    (hL : 0 < L) (hD : 0 < D) (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) :
    reflectedRobinEndpointLifetimeWorst E = L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) ↔
      (∀ j, E.geometry.site j = L * ((A.leftReactive.toNat : ℝ) + 2 * (j.val : ℝ) + 1) / A.sideTotal) ∧
      (∀ i, E.reactions.activeStrength i = K * A.homogeneousShare i) := by
  rw [reflectedRobinEndpointLifetimeWorst_eq]
  exact endpoint_homogeneous_cost_eq_iff A hL hD E

theorem reflectedRobinEndpointLifetime_homogeneous_interior_strength
    (hL : 0 < L) (hD : 0 < D) (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K)
    (hE : ∀ F : EndpointPhysicalDesign A (homogeneous L D hL hD) K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F)
    (j : Fin A.interiorCount) : E.reactions.interiorStrength j = 2 * K / A.sideTotal :=
  endpoint_homogeneous_interior_strength A hL hD E
    ((reflectedRobinEndpointLifetimeWorst_optimal_iff E).mp hE) j

theorem reflectedRobinEndpointLifetime_homogeneous_endpoint_strength
    (hL : 0 < L) (hD : 0 < D) (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K)
    (hE : ∀ F : EndpointPhysicalDesign A (homogeneous L D hL hD) K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F)
    (i : Fin A.count) (hi : A.kind i ≠ .ordinary) : E.reactions.activeStrength i = K / A.sideTotal :=
  endpoint_homogeneous_endpoint_strength A hL hD E
    ((reflectedRobinEndpointLifetimeWorst_optimal_iff E).mp hE) i hi

theorem reflectedRobinEndpointLifetime_homogeneous_site_values
    (hL : 0 < L) (hD : 0 < D) (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K)
    (hE : ∀ F : EndpointPhysicalDesign A (homogeneous L D hL hD) K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F)
    (i : Fin A.count) : reflectedRobinEndpointLifetimeExpectation E (A.physicalSite E.geometry i) = L / K :=
  (reflectedRobinEndpointMeanLifetime_eq E.equation (A.physicalSite_mem E.geometry i)).trans
    (endpoint_homogeneous_optimal_site_values A hL hD E
      ((reflectedRobinEndpointLifetimeWorst_optimal_iff E).mp hE) i)

end TimeTraps.Probability
