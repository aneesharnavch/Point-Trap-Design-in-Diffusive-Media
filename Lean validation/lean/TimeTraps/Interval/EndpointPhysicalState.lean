module

public import TimeTraps.Interval.EndpointPhysicalWeak
public import TimeTraps.Interval.PhysicalNorm
public import TimeTraps.Interval.StrictPartition

@[expose] public section

/-!
Regularity, positivity and the physical objective for the independent
endpoint weak problem. Endpoint flux signs follow from oriented incidence;
the flux is the continuous extension from each adjacent open gap. The
design objective is the actual Lebesgue essential norm, proved to be an
attained maximum. No mixed-partition optimum is assumed in these data.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {A : EndpointArchitecture} {K : ℝ}

theorem EndpointWeakEquation.to_strong {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    ∃ j, GraphEquation D.graph R.nodal (fun v => w (D.node v)) (D.gapRestriction w) j := by
  obtain ⟨U, u, j, h⟩ := graph_state_exists D.graph R.nodal R.nodal_nonneg R.nodal_anchor
  have heq := endpoint_weak_state_unique hw (D.assembledState_endpointWeak h)
  have hn (v : Fin (A.interiorCount + 2)) : w (D.node v) = U v :=
    (heq (D.node_mem v)).trans (D.assembledState_node h.energy_membership v)
  have hr := D.restrict_energy hw.energy
  refine ⟨j, ⟨?_, hr.tail_value, hr.head_value, ?_⟩⟩
  · intro e
    apply (h.edge_equation e).congr_state
    intro x hx
    exact (heq (D.gap_point_mem e hx)).trans (D.assembledState_gap h.energy_membership e hx)
  · intro v
    rw [hn]
    exact h.vertex_balance v

theorem OrderedMedium.endpointWeak_of_strong (D : OrderedMedium A.interiorCount)
    {R : EndpointReactions A K} {w : ℝ → ℝ} {j : Fin (A.interiorCount + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph R.nodal (fun v => w (D.node v)) (D.gapRestriction w) j) :
    EndpointWeakEquation D R w := by
  apply (D.assembledState_endpointWeak h).congr_state
  intro x hx
  obtain ⟨e, he⟩ := D.gap_cover hx
  have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  simpa only [OrderedMedium.gapRestriction, add_sub_cancel] using
    D.assembledState_gap h.energy_membership e ht

theorem endpoint_weak_iff_strong {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} :
    EndpointWeakEquation D R w ↔
      ∃ j, GraphEquation D.graph R.nodal (fun v => w (D.node v)) (D.gapRestriction w) j :=
  ⟨fun h => h.to_strong, fun ⟨_, h⟩ => D.endpointWeak_of_strong h⟩

theorem EndpointReactions.endpoint_flux (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) {U : Fin (A.interiorCount + 2) → ℝ}
    {u j : Fin (A.interiorCount + 1) → ℝ → ℝ} (h : GraphEquation D.graph R.nodal U u j) :
    j 0 0 = R.leftStrength * U 0 ∧
      j (Fin.last A.interiorCount) (D.gapLength (Fin.last A.interiorCount)) =
        -(R.rightStrength * U (Fin.last (A.interiorCount + 1))) := by
  have hl := h.vertex_balance 0
  have hr := h.vertex_balance (Fin.last (A.interiorCount + 1))
  change R.nodal 0 * U 0 = vertexFlux Fin.castSucc Fin.succ _ _ 0 at hl
  change R.nodal (Fin.last (A.interiorCount + 1)) * U (Fin.last (A.interiorCount + 1)) =
    vertexFlux Fin.castSucc Fin.succ _ _ (Fin.last (A.interiorCount + 1)) at hr
  rw [R.nodal_first, path_flux_first] at hl
  rw [R.nodal_last, path_flux_last] at hr
  change R.rightStrength * U (Fin.last (A.interiorCount + 1)) =
    -j (Fin.last A.interiorCount) (D.gapLength (Fin.last A.interiorCount)) at hr
  exact ⟨hl.symm, by linarith⟩

theorem EndpointReactions.interior_flux_jump (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) {U : Fin (A.interiorCount + 2) → ℝ}
    {u j : Fin (A.interiorCount + 1) → ℝ → ℝ} (h : GraphEquation D.graph R.nodal U u j)
    (i : Fin A.interiorCount) :
    j i.succ 0 - j i.castSucc (D.gapLength i.castSucc) = R.interiorStrength i * U (trapNode i) := by
  have hi := h.vertex_balance (trapNode i)
  change R.nodal (trapNode i) * U (trapNode i) = vertexFlux Fin.castSucc Fin.succ _ _ (trapNode i) at hi
  rw [R.nodal_interior, path_flux_trap] at hi
  exact hi.symm

theorem EndpointWeakEquation.physical_flux_laws {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    ∃ j, GraphEquation D.graph R.nodal (fun v => w (D.node v)) (D.gapRestriction w) j ∧
      j 0 0 = R.leftStrength * w D.source.left ∧
      j (Fin.last A.interiorCount) (D.gapLength (Fin.last A.interiorCount)) =
        -(R.rightStrength * w D.source.right) ∧
      ∀ i, j i.succ 0 - j i.castSucc (D.gapLength i.castSucc) =
        R.interiorStrength i * w (D.site i) := by
  obtain ⟨j, hj⟩ := hw.to_strong
  have he := R.endpoint_flux D hj
  refine ⟨j, hj, ?_, ?_, ?_⟩
  · simpa only [D.node_first] using he.1
  · simpa only [D.node_last] using he.2
  · intro i
    exact R.interior_flux_jump D hj i

theorem EndpointWeakEquation.positive {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    ∀ x ∈ Icc D.source.left D.source.right, 0 < w x := by
  obtain ⟨j, hj⟩ := hw.to_strong
  have hp := (hj.positive R.nodal_nonneg).2
  intro x hx
  obtain ⟨e, he⟩ := D.gap_cover hx
  have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  simpa only [OrderedMedium.gapRestriction, add_sub_cancel] using hp e _ ht

theorem EndpointWeakEquation.conservation {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    (∑ k, R.nodal k * w (D.node k)) = D.source.mass := by
  have h := hw.weak_form (fun _ => 1) (IntervalEnergy.const 1 D.source.left D.source.right)
  simpa only [deriv_const, mul_zero, intervalIntegral.integral_zero, mul_one, zero_add,
    SourceInterval.mass] using h

theorem EndpointWeakEquation.expanded_conservation {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    R.leftStrength * w D.source.left +
      (∑ i, R.interiorStrength i * w (D.site i)) +
      R.rightStrength * w D.source.right = D.source.mass := by
  have h := hw.conservation
  rw [R.nodal_pairing] at h
  simpa only [D.node_first, D.node_last, OrderedMedium.site] using h

theorem EndpointWeakEquation.energy_identity {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x ^ 2) +
      (∑ k, R.nodal k * w (D.node k) ^ 2) =
      ∫ x in D.source.left..D.source.right, D.source.density x * w x := by
  simpa only [pow_two, mul_assoc] using hw.weak_form w hw.energy

theorem EndpointWeakEquation.maximum_eq_essentialNorm {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    D.graph.stateMaximum (D.gapRestriction w) = D.essentialNorm w := by
  have hm := (D.restrict_energy hw.energy).maximum_isGreatest
  rw [D.restriction_values] at hm
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := hm.1
    rw [← he]
    exact (le_abs_self _).trans ((D.essentialNorm_le_iff hw.energy).mp le_rfl x hx)
  · apply (D.essentialNorm_le_iff hw.energy).mpr
    intro x hx
    rw [abs_of_pos (hw.positive x hx)]
    exact hm.2 ⟨x, hx, rfl⟩

theorem EndpointWeakEquation.essentialNorm_isGreatest {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    IsGreatest (w '' Icc D.source.left D.source.right) (D.essentialNorm w) := by
  rw [← hw.maximum_eq_essentialNorm, ← D.restriction_values]
  exact (D.restrict_energy hw.energy).maximum_isGreatest

structure EndpointPhysicalDesign (A : EndpointArchitecture) (B : IntervalMedium) (K : ℝ) where
  geometry : OrderedMedium A.interiorCount
  medium_eq : geometry.medium = B
  reactions : EndpointReactions A K
  state : ℝ → ℝ
  equation : EndpointWeakEquation geometry reactions state

noncomputable def EndpointPhysicalDesign.cost {B : IntervalMedium}
    (E : EndpointPhysicalDesign A B K) : ℝ := E.geometry.essentialNorm E.state

def EndpointPhysicalDesign.Optimal {B : IntervalMedium} (E : EndpointPhysicalDesign A B K) : Prop :=
  ∀ F : EndpointPhysicalDesign A B K, E.cost ≤ F.cost

noncomputable def EndpointPhysicalDesign.ofGeometry (D : OrderedMedium A.interiorCount)
    (R : EndpointReactions A K) : EndpointPhysicalDesign A D.medium K where
  geometry := D
  medium_eq := rfl
  reactions := R
  state := Classical.choose (endpoint_weak_state_exists D R)
  equation := Classical.choose_spec (endpoint_weak_state_exists D R)

theorem EndpointPhysicalDesign.cost_eq_essSup {B : IntervalMedium}
    (E : EndpointPhysicalDesign A B K) :
    E.cost = essSup (fun x => |E.state x|) (volume.restrict (Icc B.source.left B.source.right)) := by
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  change essSup (fun x => |E.state x|)
    (volume.restrict (Icc E.geometry.source.left E.geometry.source.right)) = _
  rw [hs]

theorem EndpointPhysicalDesign.cost_isGreatest {B : IntervalMedium}
    (E : EndpointPhysicalDesign A B K) :
    IsGreatest (E.state '' Icc B.source.left B.source.right) E.cost := by
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  simpa only [hs, cost] using E.equation.essentialNorm_isGreatest

theorem EndpointPhysicalDesign.cost_pos {B : IntervalMedium}
    (E : EndpointPhysicalDesign A B K) : 0 < E.cost := by
  have hx : E.geometry.source.left ∈ Icc E.geometry.source.left E.geometry.source.right :=
    ⟨le_rfl, E.geometry.source.increasing.le⟩
  exact (E.equation.positive _ hx).trans_le (E.equation.essentialNorm_isGreatest.2 ⟨_, hx, rfl⟩)

end TimeTraps.Interval
