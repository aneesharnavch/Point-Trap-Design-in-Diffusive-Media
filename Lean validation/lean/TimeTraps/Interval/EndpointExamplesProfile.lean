module

public import TimeTraps.Interval.EndpointHomogeneousCorollaries

@[expose] public section

/-! The endpoint-only homogeneous corridor has an exact quadratic
physical state. The result concerns every actual full-H1 weak design,
and specializes to the manuscript's L=2, D=1, K=4 illustration. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

theorem endpoint_leftOnly_constant_profile (B : IntervalMedium) {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value z = C) (M : ℝ)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    B.endpointPartitionProfile EndpointArchitecture.leftOnly EndpointArchitecture.leftOnly.homogeneousPartition M z =
      M - C * (1 - z) ^ 2 / 2 := by
  let A := EndpointArchitecture.leftOnly
  let Q := A.homogeneousPartition
  let i : Fin A.count := ⟨0, A.count_pos⟩
  have hi : A.kind i = .leftEndpoint := EndpointArchitecture.leftOnly_kind i
  have hc : A.reconstructionSite Q B.cellWeight i = 0 := by
    simp only [EndpointArchitecture.reconstructionSite, hi]
  have he1 : i.succ = Fin.last A.count := by apply Fin.ext; rfl
  have hβ : Q.point i.succ = 1 := by rw [he1, Q.last]
  have hbound : B.endpointPartitionProfile A Q M (Q.point i.succ) = M := by
    rw [A.gapBoundary_left i hi, B.endpointPartitionProfile_boundary]
  have hr := B.endpointPartitionProfile_right A Q M i
    (show z ∈ Icc (A.reconstructionSite Q B.cellWeight i) (Q.point i.succ) by rwa [hc, hβ])
  rw [hbound, hβ, B.cellWeight.rightRise_constant hC hz.1 le_rfl hz.2] at hr
  change B.endpointPartitionProfile A Q M z = _
  linarith

theorem endpoint_leftOnly_homogeneous_construct_state {L D K : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    (homogeneous L D hL hD).endpointPartitionState EndpointArchitecture.leftOnly
      EndpointArchitecture.leftOnly.homogeneousPartition
      (EndpointArchitecture.leftOnly.root EndpointArchitecture.leftOnly.homogeneousPartition.closed
        (homogeneous L D hL hD).cellWeight (div_pos hK (homogeneous L D hL hD).source.mass_pos)) x =
      L / K + (L * x - x ^ 2 / 2) / D := by
  have htotal : EndpointArchitecture.leftOnly.sideTotal = 1 := by
    rw [EndpointArchitecture.sideTotal_formula]
    norm_num [EndpointArchitecture.leftOnly]
  unfold IntervalMedium.endpointPartitionState
  rw [endpoint_leftOnly_constant_profile _ (fun z _ => homogeneous_weight hL hD z) _
    ((homogeneous L D hL hD).source.coordinate_mem hx)]
  rw [endpoint_homogeneous_root EndpointArchitecture.leftOnly hL hD hK, htotal,
    homogeneous_coordinate]
  field_simp [ne_of_gt hL, ne_of_gt hD, ne_of_gt hK]
  ring

theorem endpoint_leftOnly_homogeneous_state {L D K : ℝ} (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign EndpointArchitecture.leftOnly (homogeneous L D hL hD) K) :
    EqOn E.state (fun x => L / K + (L * x - x ^ 2 / 2) / D) (Icc (0 : ℝ) L) := by
  have hl : E.reactions.leftStrength = K := by
    have hs : (∑ i, E.reactions.interiorStrength i) = 0 :=
      Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
    have he := E.reactions.total_strength
    rw [hs, E.reactions.right_zero rfl, add_zero, add_zero] at he
    exact he
  have htotal : EndpointArchitecture.leftOnly.sideTotal = 1 := by
    rw [EndpointArchitecture.sideTotal_formula]
    norm_num [EndpointArchitecture.leftOnly]
  have hE : E.Optimal := by
    apply (endpoint_homogeneous_optimal_iff EndpointArchitecture.leftOnly hL hD E).mpr
    refine ⟨fun j => Fin.elim0 j, ?_⟩
    intro i
    have hi := EndpointArchitecture.leftOnly_kind i
    change E.reactions.nodal (EndpointArchitecture.leftOnly.activeNode i) = _
    rw [EndpointArchitecture.leftOnly.activeNode_left i hi, E.reactions.nodal_first, hl]
    simp only [EndpointArchitecture.homogeneousShare, EndpointArchitecture.sideCount, hi,
      reduceCtorEq, if_false, htotal, div_one, mul_one]
  have he := E.optimal_state hE
  rw [endpoint_homogeneous_optimal_partition EndpointArchitecture.leftOnly hL hD E hE] at he
  intro x hx
  exact (he hx).trans (endpoint_leftOnly_homogeneous_construct_state hL hD E.reactions.budget_pos hx)

end TimeTraps.Interval
