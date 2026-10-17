module

public import TimeTraps.Analysis.GraphRealizedSobolev
public import TimeTraps.Analysis.IntervalEndpointPolynomial

@[expose] public section

/-! Genuine graph H1 states are uniformly dense in continuous functions
on the actual compact graph. Edgewise polynomial approximation keeps all
vertex values exact, including at loops and parallel edges. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Graph

variable {V E : Type*} [Fintype E] [Nonempty E]

theorem graphRealizedSobolev_uniform_approximation (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : GraphSobolevSpace G, ‖graphRealizedSobolev G u - f‖ < ε ∧
      ∀ v, graphRealizedSobolev G u (G.vertexPoint v) = f (G.vertexPoint v) := by
  let fEdge (e : E) : C(Icc (0 : ℝ) (G.length e), ℝ) :=
    ⟨fun x => f (G.edgePoint e x), f.continuous.comp (G.edgePoint_continuous e)⟩
  have hex (e : E) := endpoint_polynomial_approximation (G.length_pos e) (fEdge e) hε
  choose p hp0 hpL hpa using hex
  let U := fun v => f (G.vertexPoint v)
  let w := fun e x => (p e).eval x
  have hw : GraphEnergy G U w := by
    refine ⟨fun e => polynomial_intervalEnergy (p e) (G.length_pos e).le, ?_, ?_⟩
    · intro e
      exact (hp0 e).trans (congrArg f (G.edgePoint_tail e))
    · intro e
      exact (hpL e).trans (congrArg f (G.edgePoint_head e))
  let u := graphSobolevSpaceOfEnergy G hw
  refine ⟨u, ?_, fun v => ?_⟩
  · apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro z
    obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective z
    change |graphRealizedSobolev G u (G.edgePoint e x) - f (G.edgePoint e x)| < ε
    rw [graphRealizedSobolev_ofEnergy G hw e x]
    exact hpa e x
  · rw [graphRealizedSobolev_vertex, graphSobolevSpaceOfEnergy_node G hw v]

theorem graphRealizedSobolev_denseRange (G : MetricGraph V E) :
    DenseRange (graphRealizedSobolev G) := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨u, hu, _⟩ := graphRealizedSobolev_uniform_approximation G f hε
  refine ⟨u, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact hu

end TimeTraps.Analysis
