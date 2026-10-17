module

public import TimeTraps.Analysis.GraphConservativeCoordinateScalar
public import TimeTraps.Analysis.GraphRealizedSobolev

@[expose] public section

/-! Scalar coordinates are genuine continuous graph H1 states. Their
continuous generators descend with value zero at every vertex, and their
edge equations retain the original conductance and physical flux. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.coordinateTest (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) : C(GraphRealization G, ℝ) :=
  ⟨fun p => φ (G.smoothCoordinates p), φ.continuous.comp G.smoothCoordinates_continuous⟩

omit [Fintype V] in
theorem MetricGraph.coordinateTest_edge (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) (x : Icc (0 : ℝ) (G.length e)) :
    G.coordinateTest φ (G.edgePoint e x) = G.coordinateEdgeValue φ e x.val := by
  change φ (G.smoothCoordinates (G.edgePoint e x)) = _
  rw [G.smoothCoordinates_edge]
  rfl

noncomputable def MetricGraph.coordinateGenerator (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) : C(GraphRealization G, ℝ) :=
  ⟨G.realizationTrace (fun e x => G.coordinateEdgeGenerator φ e x.val),
    G.realizationTrace_continuous (fun _ => (0 : ℝ)) _
      (fun e => (G.coordinateEdgeGenerator_continuous φ e).domRestrict)
      (fun e => (G.coordinateEdgeFlux_generator_endpoints φ e).2.2.1)
      (fun e => (G.coordinateEdgeFlux_generator_endpoints φ e).2.2.2)⟩

omit [Nonempty E] in
theorem MetricGraph.coordinateGenerator_edge (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) (x : Icc (0 : ℝ) (G.length e)) :
    G.coordinateGenerator φ (G.edgePoint e x) = G.coordinateEdgeGenerator φ e x.val :=
  G.realizationTrace_apply (fun _ => (0 : ℝ))
    (fun d z => G.coordinateEdgeGenerator φ d z.val)
    (fun d => (G.coordinateEdgeFlux_generator_endpoints φ d).2.2.1)
    (fun d => (G.coordinateEdgeFlux_generator_endpoints φ d).2.2.2) e x

omit [Nonempty E] in
theorem MetricGraph.coordinateEdge_equation (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) :
    EdgeEquation (G.conductance e) (fun x => -G.coordinateEdgeGenerator φ e x)
      0 (G.length e) (G.coordinateEdgeValue φ e) (G.coordinateEdgeFlux φ e) := by
  refine ⟨G.coordinateEdgeValue_continuous φ e, G.coordinateEdgeFlux_continuous φ e,
    fun _ hx => G.coordinateEdgeValue_hasDerivAt φ e hx, ?_⟩
  intro x hx
  simpa only [neg_neg] using G.coordinateEdgeFlux_hasDerivAt φ e hx

omit [Nonempty E] in
theorem MetricGraph.coordinateEnergy (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) :
    GraphEnergy G (fun v => φ (graphVertexCoordinates v)) (G.coordinateEdgeValue φ) := by
  constructor
  · intro e
    exact (G.coordinateEdge_equation φ e).state_energy (G.length_pos e).le
      (G.conductance_continuous e) (fun x hx => (G.conductance_pos e x hx).ne')
  · intro e
    unfold coordinateEdgeValue
    rw [(G.smoothResistance_endpoints e).1, G.edgeCoordinates_zero]
  · intro e
    unfold coordinateEdgeValue
    rw [(G.smoothResistance_endpoints e).2, G.edgeCoordinates_one]

noncomputable def MetricGraph.coordinateSobolev (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) : GraphSobolevSpace G :=
  graphSobolevSpaceOfEnergy G (G.coordinateEnergy φ)

theorem MetricGraph.coordinateSobolev_realized (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) :
    graphRealizedSobolev G (G.coordinateSobolev φ) = G.coordinateTest φ := by
  ext p
  obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective p
  rw [coordinateSobolev, graphRealizedSobolev_ofEnergy, G.coordinateTest_edge]

end TimeTraps.Graph
