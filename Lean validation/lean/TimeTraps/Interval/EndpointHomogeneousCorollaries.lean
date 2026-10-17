module

public import TimeTraps.Interval.EndpointHomogeneousPhysical
public import TimeTraps.Interval.EndpointParameterEquality

@[expose] public section

/-! All homogeneous optimal parameter vectors, the explicit 2m+b value,
and the four endpoint-position formulas. Indices j are zero-based. -/

namespace TimeTraps.Interval

open Set

variable (A : EndpointArchitecture) {L D K : ℝ}

theorem endpoint_homogeneous_optimal_iff (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) :
    E.Optimal ↔
      (∀ j, E.geometry.site j = L * ((A.leftReactive.toNat : ℝ) + 2 * (j.val : ℝ) + 1) / A.sideTotal) ∧
      (∀ i, E.reactions.activeStrength i = K * A.homogeneousShare i) := by
  constructor
  · intro hE
    exact ⟨endpoint_homogeneous_optimal_sites A hL hD E hE,
      endpoint_homogeneous_optimal_strengths A hL hD E hE⟩
  · rintro ⟨hsite, hκ⟩
    apply E.optimal_iff_exists_reconstruction_parameters.mpr
    refine ⟨A.homogeneousPartition, ?_, ?_, ?_⟩
    · exact (A.constant_minimizer_iff _ _ (fun z _ => homogeneous_weight hL hD z)
        (div_pos E.reactions.budget_pos (homogeneous L D hL hD).source.mass_pos)).mpr rfl
    · intro j
      exact (hsite j).trans (A.homogeneous_interior_sites hL hD j).symm
    · intro i
      exact (hκ i).trans (endpoint_homogeneous_strength A hL hD E.reactions.budget_pos i).symm

theorem endpoint_homogeneous_cost_eq_iff (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) :
    E.cost = L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) ↔
      (∀ j, E.geometry.site j = L * ((A.leftReactive.toNat : ℝ) + 2 * (j.val : ℝ) + 1) / A.sideTotal) ∧
      (∀ i, E.reactions.activeStrength i = K * A.homogeneousShare i) := by
  have he : E.cost = L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) ↔ E.Optimal := by
    constructor
    · intro h F
      rw [h]
      exact endpoint_homogeneous_lower_bound A hL hD F
    · exact endpoint_homogeneous_optimal_cost A hL hD E
  exact he.trans (endpoint_homogeneous_optimal_iff A hL hD E)

theorem endpoint_homogeneous_two_m_plus_b_minimum (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    IsLeast (range (fun E : EndpointPhysicalDesign A (homogeneous L D hL hD) K => E.cost))
      (L / K + L ^ 2 /
        (2 * D * (2 * (A.interiorCount : ℝ) + A.leftReactive.toNat + A.rightReactive.toNat) ^ 2)) := by
  rw [← A.sideTotal_formula]
  exact endpoint_homogeneous_minimum A hL hD hK

theorem endpoint_homogeneous_interior_strength (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal)
    (j : Fin A.interiorCount) : E.reactions.interiorStrength j = 2 * K / A.sideTotal := by
  have he := endpoint_homogeneous_optimal_strengths A hL hD E hE (A.interiorCell j)
  simp only [EndpointReactions.activeStrength, A.activeNode_interior, E.reactions.nodal_interior,
    EndpointArchitecture.homogeneousShare, A.sideCount_interior] at he
  rw [he]
  ring

theorem endpoint_homogeneous_endpoint_strength (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal)
    (i : Fin A.count) (hi : A.kind i ≠ .ordinary) : E.reactions.activeStrength i = K / A.sideTotal := by
  rw [endpoint_homogeneous_optimal_strengths A hL hD E hE]
  simp only [EndpointArchitecture.homogeneousShare, EndpointArchitecture.sideCount, if_neg hi]
  ring

theorem endpoint_homogeneous_strength_share (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal) (i : Fin A.count) :
    E.reactions.activeStrength i / K = E.reactions.activeShare E.geometry E.state i := by
  rw [endpoint_homogeneous_optimal_strengths A hL hD E hE,
    endpoint_homogeneous_optimal_shares A hL hD E hE]
  exact mul_div_cancel_left₀ _ (ne_of_gt E.reactions.budget_pos)

theorem endpoint_homogeneous_no_end_sites (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal)
    (hl : A.leftReactive = false) (hr : A.rightReactive = false) (j : Fin A.interiorCount) :
    E.geometry.site j = (2 * (j.val : ℝ) + 1) * L / (2 * A.interiorCount) := by
  rw [endpoint_homogeneous_optimal_sites A hL hD E hE, A.sideTotal_formula]
  simp only [hl, hr, Bool.toNat_false, Nat.cast_zero, zero_add, add_zero]
  ring

theorem endpoint_homogeneous_both_end_sites (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal)
    (hl : A.leftReactive = true) (hr : A.rightReactive = true) (j : Fin A.interiorCount) :
    E.geometry.site j = ((j.val : ℝ) + 1) * L / (A.interiorCount + 1) := by
  rw [endpoint_homogeneous_optimal_sites A hL hD E hE, A.sideTotal_formula]
  simp only [hl, hr, Bool.toNat_true, Nat.cast_one]
  rw [show 2 * (A.interiorCount : ℝ) + 1 + 1 = 2 * ((A.interiorCount : ℝ) + 1) by ring]
  field_simp
  ring

theorem endpoint_homogeneous_left_end_sites (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal)
    (hl : A.leftReactive = true) (hr : A.rightReactive = false) (j : Fin A.interiorCount) :
    E.geometry.site j = 2 * ((j.val : ℝ) + 1) * L / (2 * A.interiorCount + 1) := by
  rw [endpoint_homogeneous_optimal_sites A hL hD E hE, A.sideTotal_formula]
  simp only [hl, hr, Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, add_zero]
  ring

theorem endpoint_homogeneous_right_end_sites (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal)
    (hl : A.leftReactive = false) (hr : A.rightReactive = true) (j : Fin A.interiorCount) :
    E.geometry.site j = (2 * (j.val : ℝ) + 1) * L / (2 * A.interiorCount + 1) := by
  rw [endpoint_homogeneous_optimal_sites A hL hD E hE, A.sideTotal_formula]
  simp only [hl, hr, Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, add_zero, zero_add]
  ring

end TimeTraps.Interval
