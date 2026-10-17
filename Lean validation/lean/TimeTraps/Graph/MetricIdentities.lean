module

public import TimeTraps.Graph.MetricState

@[expose] public section

/-!
Uniqueness, positivity, source conservation and Green/energy identities for
the actual continuous-coefficient graph state. Green's identity here covers
edgewise C1 tests matching at vertices; the full H1 extension remains open.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Uniqueness of vertex values and of the state/flux on every physical edge. -/
theorem graph_state_unique {G : MetricGraph V E} {κ U W : V → ℝ}
    {u j w k : E → ℝ → ℝ} (hu : GraphEquation G κ U u j) (hw : GraphEquation G κ W w k)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    U = W ∧ ∀ e, EqOn (u e) (w e) (Icc 0 (G.length e)) ∧
      EqOn (j e) (k e) (Icc 0 (G.length e)) := by
  obtain ⟨X, _, hX⟩ := G.vertex_existsUnique κ hκ hanchor
  have hUW : U = W := (hX U hu.vertex_system).trans (hX W hw.vertex_system).symm
  refine ⟨hUW, ?_⟩
  intro e
  apply edge_solution_unique (hu.edge_equation e) (hw.edge_equation e) (G.length_pos e)
    (G.conductance_continuous e) (G.source_continuous e) (G.conductance_pos e)
  · rw [hu.tail_value, hw.tail_value, hUW]
  · rw [hu.head_value, hw.head_value, hUW]

theorem GraphEquation.positive [Nonempty E] {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (hκ : ∀ v, 0 ≤ κ v) :
    (∀ v, 0 < U v) ∧ ∀ e x, x ∈ Icc 0 (G.length e) → 0 < u e x := by
  let : Nonempty V := ⟨G.tail (Classical.choice inferInstance)⟩
  have hU : ∀ v, 0 < U v := vertex_solution_pos G.weight κ G.load U
    (incidenceWeight_nonneg G.tail G.head _ (fun e => (one_div_pos.mpr (G.resistance_pos e)).le))
    hκ G.load_pos h.vertex_system
  refine ⟨hU, ?_⟩
  intro e
  apply (h.edge_equation e).state_pos (G.conductance_pos e)
    (fun x hx => G.source_pos e x ⟨hx.1.le, hx.2.le⟩)
  · rw [h.tail_value]
    exact hU _
  · rw [h.head_value]
    exact hU _

/-- Total vertex absorption equals the integrated source over all edges. -/
theorem GraphEquation.conservation {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) :
    ∑ v, κ v * U v = G.totalMass := by
  exact (vertex_conservation G.weight κ U G.load
    (incidenceWeight_symmetric G.tail G.head _) h.vertex_system).trans G.load_sum

/-- Summed integration by parts with continuous, edgewise C1 test functions. -/
theorem GraphEquation.green_identity {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j)
    (Ψ : V → ℝ) (ψ ψ' : E → ℝ → ℝ)
    (hψ : ∀ e, ContinuousOn (ψ e) (Icc 0 (G.length e)))
    (hψ' : ∀ e, ContinuousOn (ψ' e) (Icc 0 (G.length e)))
    (hdψ : ∀ e x, x ∈ Ioo 0 (G.length e) → HasDerivAt (ψ e) (ψ' e x) x)
    (htail : ∀ e, ψ e 0 = Ψ (G.tail e))
    (hhead : ∀ e, ψ e (G.length e) = Ψ (G.head e)) :
    (∑ e, ∫ x in 0..G.length e, j e x * ψ' e x) + (∑ v, κ v * U v * Ψ v) =
      ∑ e, ∫ x in 0..G.length e, G.source e x * ψ e x := by
  have hedge : ∀ e, (∫ x in 0..G.length e, j e x * ψ' e x) =
      (∫ x in 0..G.length e, G.source e x * ψ e x) +
        (j e (G.length e) * Ψ (G.head e) - j e 0 * Ψ (G.tail e)) := by
    intro e
    have he := (h.edge_equation e).green_identity (G.length_pos e).le (G.source_continuous e)
      (ψ e) (ψ' e) (hψ e) (hψ' e) (hdψ e)
    rw [htail e, hhead e] at he
    linarith
  have hboundary : (∑ e, (j e (G.length e) * Ψ (G.head e) - j e 0 * Ψ (G.tail e))) =
      -(∑ v, κ v * U v * Ψ v) := by
    rw [incidence_boundary_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    rw [← h.vertex_balance v]
    ring
  simp_rw [hedge]
  rw [Finset.sum_add_distrib, hboundary]
  ring

/-- Energy is obtained by testing with the constructed state itself. -/
theorem GraphEquation.energy_identity {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) :
    (∑ e, ∫ x in 0..G.length e, j e x ^ 2 / G.conductance e x) + (∑ v, κ v * U v ^ 2) =
      ∑ e, ∫ x in 0..G.length e, G.source e x * u e x := by
  have hid := h.green_identity U u (fun e x => j e x / G.conductance e x)
    (fun e => (h.edge_equation e).state_continuous)
    (fun e => (h.edge_equation e).flux_continuous.div (G.conductance_continuous e)
      (fun x hx => ne_of_gt (G.conductance_pos e x hx)))
    (fun e => (h.edge_equation e).state_derivative) h.tail_value h.head_value
  have he : (∑ e, ∫ x in 0..G.length e, j e x ^ 2 / G.conductance e x) =
      ∑ e, ∫ x in 0..G.length e, j e x * (j e x / G.conductance e x) := by
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hv : (∑ v, κ v * U v ^ 2) = ∑ v, κ v * U v * U v := by
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he, hv]
  exact hid

end TimeTraps.Graph
