module

public import TimeTraps.Graph.Incidence
public import TimeTraps.Analysis.EdgePositivity
public import TimeTraps.Analysis.EdgeGreenIdentity

@[expose] public section

/-!
A connected finite metric graph with continuous, strictly positive edge
conductance and source. Vertex conditions use the two oriented ends of each
edge. State existence is derived from the independent vertex linear system.
The energy-space weak formulation is not part of the input data.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*}

structure MetricGraph (V E : Type*) where
  tail : E → V
  head : E → V
  length : E → ℝ
  length_pos : ∀ e, 0 < length e
  conductance : E → ℝ → ℝ
  source : E → ℝ → ℝ
  conductance_continuous : ∀ e, ContinuousOn (conductance e) (Icc 0 (length e))
  source_continuous : ∀ e, ContinuousOn (source e) (Icc 0 (length e))
  conductance_pos : ∀ e x, x ∈ Icc 0 (length e) → 0 < conductance e x
  source_pos : ∀ e x, x ∈ Icc 0 (length e) → 0 < source e x
  connected : IncidenceConnected tail head

noncomputable def MetricGraph.resistance (G : MetricGraph V E) (e : E) : ℝ :=
  resistancePrimitive (G.conductance e) 0 (G.length e)

noncomputable def MetricGraph.leftLoad (G : MetricGraph V E) (e : E) : ℝ :=
  leftSourceLoad (G.conductance e) (G.source e) 0 (G.length e)

noncomputable def MetricGraph.rightLoad (G : MetricGraph V E) (e : E) : ℝ :=
  rightSourceLoad (G.conductance e) (G.source e) 0 (G.length e)

noncomputable def MetricGraph.weight [Fintype E] (G : MetricGraph V E) : V → V → ℝ :=
  incidenceWeight G.tail G.head (fun e => 1 / G.resistance e)

noncomputable def MetricGraph.load [Fintype E] (G : MetricGraph V E) : V → ℝ :=
  incidenceLoad G.tail G.head G.leftLoad G.rightLoad

noncomputable def MetricGraph.totalMass [Fintype E] (G : MetricGraph V E) : ℝ :=
  ∑ e, sourcePrimitive (G.source e) 0 (G.length e)

noncomputable def MetricGraph.reconstructedState (G : MetricGraph V E) (U : V → ℝ) : E → ℝ → ℝ :=
  fun e => edgeState (G.conductance e) (G.source e) 0 (G.length e) (U (G.tail e)) (U (G.head e))

noncomputable def MetricGraph.reconstructedFlux (G : MetricGraph V E) (U : V → ℝ) : E → ℝ → ℝ :=
  fun e => edgeFlux (G.conductance e) (G.source e) 0 (G.length e) (U (G.tail e)) (U (G.head e))

/-- The differential equation, endpoint matching and Kirchhoff reaction law.
No solution formula, positivity, conservation or energy identity is assumed. -/
structure GraphEquation [Fintype E] (G : MetricGraph V E) (κ U : V → ℝ) (u j : E → ℝ → ℝ) : Prop where
  edge_equation : ∀ e, EdgeEquation (G.conductance e) (G.source e) 0 (G.length e) (u e) (j e)
  tail_value : ∀ e, u e 0 = U (G.tail e)
  head_value : ∀ e, u e (G.length e) = U (G.head e)
  vertex_balance : ∀ v, κ v * U v =
    vertexFlux G.tail G.head (fun e => j e 0) (fun e => j e (G.length e)) v

theorem MetricGraph.resistance_pos (G : MetricGraph V E) (e : E) : 0 < G.resistance e :=
  TimeTraps.Analysis.resistance_pos (G.length_pos e) (G.conductance_continuous e)
    (G.conductance_pos e)

theorem MetricGraph.loads_pos (G : MetricGraph V E) (e : E) :
    0 < G.leftLoad e ∧ 0 < G.rightLoad e :=
  source_loads_pos (G.length_pos e) (G.conductance_continuous e) (G.source_continuous e)
    (G.conductance_pos e) (G.source_pos e)

theorem MetricGraph.load_pos [Fintype E] [Nonempty E] (G : MetricGraph V E) (v : V) : 0 < G.load v :=
  incidenceLoad_pos G.tail G.head G.leftLoad G.rightLoad
    (fun e => (G.loads_pos e).1) (fun e => (G.loads_pos e).2) G.connected v

theorem MetricGraph.load_sum [Fintype V] [Fintype E] (G : MetricGraph V E) : ∑ v, G.load v = G.totalMass := by
  rw [MetricGraph.load, incidenceLoad_sum]
  unfold MetricGraph.totalMass
  apply Finset.sum_congr rfl
  intro e _
  exact source_loads_sum (G.conductance e) (G.source e) 0 (G.length e)

theorem MetricGraph.vertex_existsUnique [Fintype V] [Fintype E] (G : MetricGraph V E) (κ : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    ∃! U, vertexOperator G.weight κ U = G.load := by
  exact vertex_solution_existsUnique G.weight κ G.load
    (incidenceWeight_symmetric G.tail G.head _)
    (incidenceWeight_nonneg G.tail G.head _ (fun e => (one_div_pos.mpr (G.resistance_pos e)).le))
    hκ hanchor (incidence_connected_weights G.tail G.head _
      (fun e => one_div_pos.mpr (G.resistance_pos e)) G.connected)

theorem MetricGraph.reconstructed_endpoint_fluxes (G : MetricGraph V E) (U : V → ℝ) (e : E) :
    G.reconstructedFlux U e 0 =
      (1 / G.resistance e) * (U (G.head e) - U (G.tail e)) + G.leftLoad e ∧
    G.reconstructedFlux U e (G.length e) =
      (1 / G.resistance e) * (U (G.head e) - U (G.tail e)) - G.rightLoad e := by
  have h := edge_endpoint_fluxes (G.conductance e) (G.source e) 0 (G.length e)
    (U (G.tail e)) (U (G.head e))
  simpa only [MetricGraph.reconstructedFlux, MetricGraph.resistance,
    MetricGraph.leftLoad, MetricGraph.rightLoad, div_eq_mul_inv, one_mul, mul_comm] using h

theorem MetricGraph.reconstructed_graph_equation [Fintype V] [Fintype E] (G : MetricGraph V E) (κ U : V → ℝ)
    (hU : vertexOperator G.weight κ U = G.load) :
    GraphEquation G κ U (G.reconstructedState U) (G.reconstructedFlux U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    exact reconstructed_edge_equation (G.length_pos e).le (G.conductance_continuous e)
      (G.source_continuous e) (fun x hx => ne_of_gt (G.conductance_pos e x hx)) _ _
  · intro e
    exact edgeState_left _ _ _ _ _ _
  · intro e
    exact edgeState_right _ _ _ _ _ _ (ne_of_gt (G.resistance_pos e))
  · intro v
    have h₀ : (fun e => G.reconstructedFlux U e 0) =
        fun e => 1 / G.resistance e * (U (G.head e) - U (G.tail e)) + G.leftLoad e :=
      funext fun e => (G.reconstructed_endpoint_fluxes U e).1
    have h₁ : (fun e => G.reconstructedFlux U e (G.length e)) =
        fun e => 1 / G.resistance e * (U (G.head e) - U (G.tail e)) - G.rightLoad e :=
      funext fun e => (G.reconstructed_endpoint_fluxes U e).2
    rw [h₀, h₁]
    exact (incidence_flux_balance G.tail G.head _ _ _ κ U v).mpr (congrFun hU v)

theorem GraphEquation.edge_reconstruction [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (e : E) :
    EqOn (u e) (G.reconstructedState U e) (Icc 0 (G.length e)) ∧
      EqOn (j e) (G.reconstructedFlux U e) (Icc 0 (G.length e)) := by
  apply edge_solution_unique (h.edge_equation e)
    (reconstructed_edge_equation (G.length_pos e).le (G.conductance_continuous e)
      (G.source_continuous e) (fun x hx => ne_of_gt (G.conductance_pos e x hx)) _ _)
    (G.length_pos e) (G.conductance_continuous e) (G.source_continuous e) (G.conductance_pos e)
  · exact (h.tail_value e).trans (edgeState_left _ _ _ _ _ _).symm
  · exact (h.head_value e).trans
      (edgeState_right _ _ _ _ _ _ (ne_of_gt (G.resistance_pos e))).symm

/-- An actual state necessarily solves the derived finite system. -/
theorem GraphEquation.vertex_system [Fintype V] [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ} {u j : E → ℝ → ℝ}
    (h : GraphEquation G κ U u j) : vertexOperator G.weight κ U = G.load := by
  ext v
  apply (incidence_flux_balance G.tail G.head _ _ _ κ U v).mp
  have h₀ : (fun e => j e 0) =
      fun e => 1 / G.resistance e * (U (G.head e) - U (G.tail e)) + G.leftLoad e := by
    funext e
    exact ((h.edge_reconstruction e).2 ⟨le_rfl, (G.length_pos e).le⟩).trans
      (G.reconstructed_endpoint_fluxes U e).1
  have h₁ : (fun e => j e (G.length e)) =
      fun e => 1 / G.resistance e * (U (G.head e) - U (G.tail e)) - G.rightLoad e := by
    funext e
    exact ((h.edge_reconstruction e).2 ⟨(G.length_pos e).le, le_rfl⟩).trans
      (G.reconstructed_endpoint_fluxes U e).2
  simpa only [h₀, h₁] using h.vertex_balance v

theorem graph_state_exists [Fintype V] [Fintype E] (G : MetricGraph V E) (κ : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    ∃ U u j, GraphEquation G κ U u j := by
  obtain ⟨U, hU, _⟩ := G.vertex_existsUnique κ hκ hanchor
  exact ⟨U, G.reconstructedState U, G.reconstructedFlux U,
    G.reconstructed_graph_equation κ U hU⟩

end TimeTraps.Graph
