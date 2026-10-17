module

public import TimeTraps.Graph.ConstantEdge
public import TimeTraps.Graph.PassiveTip
public import TimeTraps.Graph.WeakIdentities

@[expose] public section

/-!
The sharp mass-resistance inequalities for the actual weak graph state.
Constant coefficients are required only on each physical edge. Every edge
barrier is derived from its equation and the incidence-defined tip condition.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*}

structure EdgeConstants (G : MetricGraph V E) where
  conductance : E → ℝ
  source : E → ℝ
  conductance_eq : ∀ e, EqOn (G.conductance e) (fun _ => conductance e) (Icc 0 (G.length e))
  source_eq : ∀ e, EqOn (G.source e) (fun _ => source e) (Icc 0 (G.length e))

theorem EdgeConstants.conductance_pos {G : MetricGraph V E} (c : EdgeConstants G) (e : E) :
    0 < c.conductance e := by
  have hp := G.conductance_pos e 0 ⟨le_rfl, (G.length_pos e).le⟩
  rwa [c.conductance_eq e ⟨le_rfl, (G.length_pos e).le⟩] at hp

theorem EdgeConstants.source_pos {G : MetricGraph V E} (c : EdgeConstants G) (e : E) :
    0 < c.source e := by
  have hp := G.source_pos e 0 ⟨le_rfl, (G.length_pos e).le⟩
  rwa [c.source_eq e ⟨le_rfl, (G.length_pos e).le⟩] at hp

theorem EdgeConstants.mass_eq {G : MetricGraph V E} (c : EdgeConstants G) (e : E) :
    G.edgeMass e = c.source e * G.length e := by
  change (∫ x in 0..G.length e, G.source e x) = _
  calc
    _ = ∫ _ in 0..G.length e, c.source e := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact c.source_eq e (by simpa only [uIcc_of_le (G.length_pos e).le] using hx)
    _ = _ := by simp [mul_comm]

theorem EdgeConstants.resistance_eq {G : MetricGraph V E} (c : EdgeConstants G) (e : E) :
    G.resistance e = G.length e / c.conductance e := by
  change (∫ x in 0..G.length e, 1 / G.conductance e x) = _
  calc
    _ = ∫ _ in 0..G.length e, 1 / c.conductance e := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [c.conductance_eq e (by simpa only [uIcc_of_le (G.length_pos e).le] using hx)]
    _ = _ := by simp [div_eq_mul_inv]

theorem EdgeConstants.flux_cost_eq {G : MetricGraph V E} (c : EdgeConstants G)
    (u j : E → ℝ → ℝ) (M : ℝ) (e : E) :
    G.edgeCost u j M e = ∫ x in 0..G.length e,
      (c.source e * (M - u e x) + j e x ^ 2 / c.conductance e) := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc 0 (G.length e) := by simpa only [uIcc_of_le (G.length_pos e).le] using hx
  dsimp only
  rw [c.source_eq e hxI, c.conductance_eq e hxI]

/-- The Neumann enhancement is selected from degree-one passive incidence,
not supplied as an unproved edge-bound hypothesis. -/
theorem GraphEquation.sharp_edge_barrier [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j)
    (c : EdgeConstants G) (M : ℝ) (e : E) (hM : ∀ x ∈ Icc 0 (G.length e), u e x ≤ M) :
    G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8 ≤ G.weakEdgeCost u M e := by
  classical
  have he := constant_edge_of_eqOn (h.edge_equation e) (c.conductance_eq e) (c.source_eq e)
  rw [h.weakEdgeCost_eq M e, c.flux_cost_eq u j M e, MetricGraph.adjustedResistance,
    c.resistance_eq e, c.mass_eq e]
  unfold MetricGraph.reflectionFactor
  split_ifs with htip
  · have hscale : (4 * (G.length e / c.conductance e)) * (c.source e * G.length e) ^ 2 / 8 =
        (c.source e * G.length e) ^ 2 * (G.length e / c.conductance e) / 2 := by ring
    rw [hscale]
    rcases htip with ht | ht
    · exact (constant_edge_reflecting_left he (c.conductance_pos e) (c.source_pos e)
        (G.length_pos e) hM (h.passive_tail_neumann ht)).1
    · exact (constant_edge_reflecting_right he (c.conductance_pos e) (c.source_pos e)
        (G.length_pos e) hM (h.passive_head_neumann ht)).1
  · rw [one_mul, mul_comm (G.length e / c.conductance e)]
    exact (constant_edge_ordinary_barrier he (c.conductance_pos e) (c.source_pos e)
      (G.length_pos e) hM).1

theorem WeakGraphEquation.sharp_edge_barrier [Fintype V] [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (M : ℝ) (e : E) (hM : ∀ x ∈ Icc 0 (G.length e), u e x ≤ M) :
    G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8 ≤ G.weakEdgeCost u M e := by
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  exact hj.sharp_edge_barrier c M e hM

/-- Both mass-resistance bounds for every upper bound of the physical state.
All conservation, energy and edge premises are discharged by the weak equation. -/
theorem WeakGraphEquation.mass_resistance_bounds [Fintype V] [Fintype E] [Nonempty E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    {M : ℝ} (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) :
    G.totalMass / (∑ v, κ v) +
      (∑ e, G.adjustedResistance κ e * G.edgeMass e ^ 2) / (8 * G.totalMass) ≤ M ∧
    G.totalMass / (∑ v, κ v) + G.totalMass / (8 * ∑ e, 1 / G.adjustedResistance κ e) ≤
      G.totalMass / (∑ v, κ v) +
        (∑ e, G.adjustedResistance κ e * G.edgeMass e ^ 2) / (8 * G.totalMass) := by
  have hK : 0 < ∑ v, κ v := by
    obtain ⟨v, hv⟩ := hanchor
    exact Finset.sum_pos' (fun w _ => hκ w) ⟨v, Finset.mem_univ v, hv⟩
  have hC : 0 < ∑ e, 1 / G.adjustedResistance κ e :=
    Finset.sum_pos (fun e _ => one_div_pos.mpr (G.adjustedResistance_pos κ e)) Finset.univ_nonempty
  exact finite_graph_bounds κ U (G.adjustedResistance κ) G.edgeMass (G.weakEdgeCost u M)
    G.totalMass_pos hK hC hκ (G.adjustedResistance_pos κ) rfl h.conservation rfl rfl
    (fun e => h.sharp_edge_barrier c hκ hanchor M e (hM e))
    (h.cost_energy_identity hκ hanchor M)

theorem WeakGraphEquation.edge_excess_nonneg [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    {M : ℝ} (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) (e : E) :
    0 ≤ G.weakEdgeCost u M e - G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8 :=
  sub_nonneg.mpr (h.sharp_edge_barrier c hκ hanchor M e (hM e))

end TimeTraps.Graph
