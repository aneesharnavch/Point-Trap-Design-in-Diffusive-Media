module

public import TimeTraps.Analysis.SourceEdgeEquation
public import TimeTraps.Graph.StateMaximum

@[expose] public section

/-!
Source-coordinate reduction for the existing continuous-coefficient metric
graph and its independent weak equation. The actual integral cost, norm,
and incidence-derived passive conditions are retained by the reduction.
The sharp minimization of the resulting profile-sensitive cost is separate.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis

variable {V E : Type*}

def MetricGraph.sourceInterval (G : MetricGraph V E) (e : E) : SourceInterval where
  left := 0
  right := G.length e
  increasing := G.length_pos e
  density := G.source e
  continuous := G.source_continuous e
  positive := G.source_pos e

noncomputable def MetricGraph.sourceWeight (G : MetricGraph V E) (e : E) : ℝ → ℝ :=
  (G.sourceInterval e).weight (G.conductance e)

theorem MetricGraph.sourceInterval_mass (G : MetricGraph V E) (e : E) :
    (G.sourceInterval e).mass = G.edgeMass e := rfl

theorem MetricGraph.sourceWeight_pos (G : MetricGraph V E) (e : E) (z : ℝ) :
    0 < G.sourceWeight e z := (G.sourceInterval e).weight_pos (G.conductance_pos e) z

theorem MetricGraph.sourceWeight_continuous (G : MetricGraph V E) (e : E) :
    Continuous (G.sourceWeight e) :=
  (G.sourceInterval e).weight_continuous (G.conductance_continuous e) (G.conductance_pos e)

theorem MetricGraph.sourceWeight_integral (G : MetricGraph V E) (e : E) :
    (∫ z in 0..1, G.sourceWeight e z) = G.edgeMass e * G.resistance e :=
  (G.sourceInterval e).weight_integral (G.conductance_continuous e) (G.conductance_pos e)

theorem EdgeConstants.sourceWeight_eq {G : MetricGraph V E} (c : EdgeConstants G) (e : E) (z : ℝ) :
    G.sourceWeight e z = G.edgeMass e * G.resistance e := by
  have hx : (G.sourceInterval e).inverse z ∈ Icc 0 (G.length e) :=
    (G.sourceInterval e).inverse_mem z
  change (G.sourceInterval e).mass ^ 2 /
    (G.conductance e ((G.sourceInterval e).inverse z) *
      G.source e ((G.sourceInterval e).inverse z)) = _
  rw [c.conductance_eq e hx, c.source_eq e hx, G.sourceInterval_mass, c.mass_eq e, c.resistance_eq e]
  field_simp [ne_of_gt (c.conductance_pos e), ne_of_gt (c.source_pos e)]

theorem GraphEquation.source_flux [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (e : E) {z : ℝ} (hz : z ∈ Icc 0 1) :
    (G.sourceInterval e).transformed (j e) z =
      G.edgeMass e * ((G.sourceInterval e).fluxLevel (j e) - z) :=
  (G.sourceInterval e).transformed_flux (h.edge_equation e) hz

theorem GraphEquation.source_state_derivative [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (e : E) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt ((G.sourceInterval e).transformed (u e))
      (G.sourceWeight e z * ((G.sourceInterval e).fluxLevel (j e) - z)) z :=
  (G.sourceInterval e).transformed_state_derivative (h.edge_equation e) (G.conductance_pos e) hz

theorem GraphEquation.source_deficit_derivative [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (M : ℝ) (e : E) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (fun w => M - (G.sourceInterval e).transformed (u e) w)
      (G.sourceWeight e z * (z - (G.sourceInterval e).fluxLevel (j e))) z :=
  (G.sourceInterval e).transformed_deficit_derivative (h.edge_equation e) (G.conductance_pos e) M hz

theorem GraphEquation.source_edge_cost [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (M : ℝ) (e : E) :
    G.edgeCost u j M e = G.edgeMass e * ∫ z in 0..1,
      (M - (G.sourceInterval e).transformed (u e) z +
        G.sourceWeight e z * (z - (G.sourceInterval e).fluxLevel (j e)) ^ 2) :=
  (G.sourceInterval e).edge_cost_transport (h.edge_equation e)
    (G.conductance_continuous e) (G.conductance_pos e) M

theorem GraphEquation.passive_tail_source_level [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) {e : E}
    (htip : G.IsPassiveTip κ (G.tail e)) : (G.sourceInterval e).fluxLevel (j e) = 0 :=
  (G.sourceInterval e).passive_left_fluxLevel (j e) (h.passive_tail_neumann htip)

theorem GraphEquation.passive_head_source_level [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) {e : E}
    (htip : G.IsPassiveTip κ (G.head e)) : (G.sourceInterval e).fluxLevel (j e) = 1 :=
  (G.sourceInterval e).passive_right_fluxLevel (h.edge_equation e) (h.passive_head_neumann htip)

theorem GraphEnergy.source_deficit_nonneg [Fintype E] [Nonempty E] {G : MetricGraph V E}
    {U : V → ℝ} {u : E → ℝ → ℝ} (h : GraphEnergy G U u) (e : E) (z : ℝ) :
    0 ≤ G.essentialNorm u - (G.sourceInterval e).transformed (u e) z := by
  have hx : (G.sourceInterval e).inverse z ∈ Icc 0 (G.length e) :=
    (G.sourceInterval e).inverse_mem z
  exact sub_nonneg.mpr ((le_abs_self _).trans
    (h.essentialNorm_le_iff.mp (le_refl (G.essentialNorm u)) e _ hx))

theorem GraphEnergy.source_maximum_attained [Fintype E] [Nonempty E] {G : MetricGraph V E}
    {U : V → ℝ} {u : E → ℝ → ℝ} (h : GraphEnergy G U u) :
    ∃ e z, z ∈ Icc 0 1 ∧ (G.sourceInterval e).transformed (u e) z = G.stateMaximum u := by
  obtain ⟨e, x, hx, hm⟩ := h.maximum_attained
  refine ⟨e, (G.sourceInterval e).coordinate x, (G.sourceInterval e).coordinate_mem hx, ?_⟩
  rw [(G.sourceInterval e).transformed_coordinate (u e) hx]
  exact hm

/-- Every weak state has the physical flux witness and the exact transformed
cost/derivative identities. No transformed-profile assumption is added. -/
theorem WeakGraphEquation.source_reduction [Fintype V] [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    ∃ j, GraphEquation G κ U u j ∧ ∀ e,
      (∀ z ∈ Ioo 0 1, HasDerivAt ((G.sourceInterval e).transformed (u e))
        (G.sourceWeight e z * ((G.sourceInterval e).fluxLevel (j e) - z)) z) ∧
      (∀ M, G.weakEdgeCost u M e = G.edgeMass e * ∫ z in 0..1,
        (M - (G.sourceInterval e).transformed (u e) z +
          G.sourceWeight e z * (z - (G.sourceInterval e).fluxLevel (j e)) ^ 2)) := by
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  refine ⟨j, hj, fun e => ⟨fun z hz => hj.source_state_derivative e hz, fun M => ?_⟩⟩
  rw [hj.weakEdgeCost_eq M e]
  exact hj.source_edge_cost M e

end TimeTraps.Graph
