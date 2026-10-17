module

public import TimeTraps.Graph.MetricIdentities
public import TimeTraps.Graph.FiniteBounds

@[expose] public section

/-!
The physical integral cost and its exact energy/deficit identities. The
identities hold for every real height M. Interpreting M as the maximum and
proving the sharp edge-cost inequalities are separate obligations.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*} [Fintype E]

noncomputable def MetricGraph.edgeMass (G : MetricGraph V E) (e : E) : ℝ :=
  sourcePrimitive (G.source e) 0 (G.length e)

noncomputable def MetricGraph.edgeCost (G : MetricGraph V E) (u j : E → ℝ → ℝ)
    (M : ℝ) (e : E) : ℝ :=
  ∫ x in 0..G.length e, (G.source e x * (M - u e x) + j e x ^ 2 / G.conductance e x)

omit [Fintype E] in
theorem MetricGraph.edgeMass_pos (G : MetricGraph V E) (e : E) : 0 < G.edgeMass e := by
  apply intervalIntegral.integral_pos (G.length_pos e) (G.source_continuous e)
  · intro x hx
    exact (G.source_pos e x ⟨hx.1.le, hx.2⟩).le
  · exact ⟨0, ⟨le_rfl, (G.length_pos e).le⟩,
      G.source_pos e 0 ⟨le_rfl, (G.length_pos e).le⟩⟩

theorem MetricGraph.totalMass_pos [Nonempty E] (G : MetricGraph V E) : 0 < G.totalMass := by
  exact Finset.sum_pos (fun e _ => G.edgeMass_pos e) Finset.univ_nonempty

theorem GraphEquation.edge_cost_formula {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (M : ℝ) (e : E) :
    G.edgeCost u j M e = M * G.edgeMass e -
      (∫ x in 0..G.length e, G.source e x * u e x) +
      (∫ x in 0..G.length e, j e x ^ 2 / G.conductance e x) := by
  have hiF : IntervalIntegrable (fun x => M * G.source e x) volume 0 (G.length e) :=
    (continuousOn_const.mul (G.source_continuous e)).intervalIntegrable_of_Icc (G.length_pos e).le
  have hiU : IntervalIntegrable (fun x => G.source e x * u e x) volume 0 (G.length e) :=
    ((G.source_continuous e).mul (h.edge_equation e).state_continuous).intervalIntegrable_of_Icc
      (G.length_pos e).le
  have hiE : IntervalIntegrable (fun x => j e x ^ 2 / G.conductance e x) volume 0 (G.length e) :=
    (((h.edge_equation e).flux_continuous.pow 2).div (G.conductance_continuous e)
      (fun x hx => ne_of_gt (G.conductance_pos e x hx))).intervalIntegrable_of_Icc (G.length_pos e).le
  calc
    _ = ∫ x in 0..G.length e,
        ((M * G.source e x - G.source e x * u e x) + j e x ^ 2 / G.conductance e x) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hiF.sub hiU) hiE,
        intervalIntegral.integral_sub hiF hiU, intervalIntegral.integral_const_mul]
      rfl

/-- The paper's graph-energy identity, for the independently defined integral cost. -/
theorem GraphEquation.cost_energy_identity [Fintype V] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (M : ℝ) :
    G.totalMass * M = (∑ v, κ v * U v ^ 2) + ∑ e, G.edgeCost u j M e := by
  have hcost : (∑ e, G.edgeCost u j M e) =
      M * G.totalMass - (∑ e, ∫ x in 0..G.length e, G.source e x * u e x) +
        (∑ e, ∫ x in 0..G.length e, j e x ^ 2 / G.conductance e x) := by
    simp_rw [h.edge_cost_formula M]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [hcost]
  have hid := h.energy_identity
  linarith

/-- The normalized three-term identity for an actual graph state. Here t is
any positive edge scale; its sharp choice χ times resistance and the signs of
the edge excesses still require the ordinary/passive-tip barrier bridge. -/
theorem GraphEquation.deficit_normalized [Fintype V] [Nonempty E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u j : E → ℝ → ℝ}
    (h : GraphEquation G κ U u j) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (t : E → ℝ) (ht : ∀ e, 0 < t e) (M : ℝ) :
    M - G.totalMass / (∑ v, κ v) - G.totalMass / (8 * ∑ e, 1 / t e) =
      G.totalMass / (∑ v, κ v) * ((1 / 2 : ℝ) * ∑ v, ∑ w,
        (κ v * U v / G.totalMass) * (κ w * U w / G.totalMass) *
          (U v - U w) ^ 2 / (U v * U w)) +
      (∑ e, (G.edgeCost u j M e - t e * G.edgeMass e ^ 2 / 8)) / G.totalMass +
      (∑ e, 1 / t e) / (8 * G.totalMass) *
        (∑ e, 1 / (t e * ∑ d, 1 / t d) *
          (t e * G.edgeMass e - G.totalMass / (∑ d, 1 / t d)) ^ 2) := by
  have hK : 0 < ∑ v, κ v := by
    obtain ⟨v, hv⟩ := hanchor
    exact Finset.sum_pos' (fun w _ => hκ w) ⟨v, Finset.mem_univ v, hv⟩
  have hC : 0 < ∑ e, 1 / t e :=
    Finset.sum_pos (fun e _ => one_div_pos.mpr (ht e)) Finset.univ_nonempty
  exact finite_graph_deficit_normalized κ U t G.edgeMass (G.edgeCost u j M)
    (ne_of_gt G.totalMass_pos) (ne_of_gt hK) (ne_of_gt hC)
    (fun v => ne_of_gt ((h.positive hκ).1 v)) ht rfl h.conservation rfl rfl
    (h.cost_energy_identity M)

end TimeTraps.Graph
