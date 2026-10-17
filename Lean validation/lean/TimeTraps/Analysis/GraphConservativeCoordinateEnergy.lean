module

public import TimeTraps.Analysis.GraphConservativeCoordinateTestData

@[expose] public section

/-! The squared-gradient coefficient of each actual graph coordinate is
continuous on the compact realization, including at vertices. It retains
the physical conductance: Gamma(F)=a(F')^2=J^2/a. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def MetricGraph.coordinateEdgeEnergyDensity (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) (x : ℝ) : ℝ :=
  G.coordinateEdgeFlux φ e x ^ 2 / G.conductance e x

theorem MetricGraph.coordinateEdgeEnergyDensity_continuous (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) :
    ContinuousOn (G.coordinateEdgeEnergyDensity φ e) (Icc 0 (G.length e)) :=
  ((G.coordinateEdgeFlux_continuous φ e).pow 2).div
    (G.conductance_continuous e) (fun x hx => (G.conductance_pos e x hx).ne')

omit [Fintype V] [Fintype E] in
theorem MetricGraph.coordinateEdgeEnergyDensity_endpoints (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) :
    G.coordinateEdgeEnergyDensity φ e 0 = 0 ∧
      G.coordinateEdgeEnergyDensity φ e (G.length e) = 0 := by
  simp only [coordinateEdgeEnergyDensity, (G.coordinateEdgeFlux_generator_endpoints φ e).1,
    (G.coordinateEdgeFlux_generator_endpoints φ e).2.1,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, and_self]

noncomputable def MetricGraph.coordinateEnergyDensity (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) : C(GraphRealization G, ℝ) :=
  ⟨G.realizationTrace (fun e x => G.coordinateEdgeEnergyDensity φ e x.val),
    G.realizationTrace_continuous (fun _ => (0 : ℝ)) _
      (fun e => (G.coordinateEdgeEnergyDensity_continuous φ e).domRestrict)
      (fun e => (G.coordinateEdgeEnergyDensity_endpoints φ e).1)
      (fun e => (G.coordinateEdgeEnergyDensity_endpoints φ e).2)⟩

theorem MetricGraph.coordinateEnergyDensity_edge (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) (x : Icc (0 : ℝ) (G.length e)) :
    G.coordinateEnergyDensity φ (G.edgePoint e x) = G.coordinateEdgeEnergyDensity φ e x.val :=
  G.realizationTrace_apply (fun _ => (0 : ℝ))
    (fun d z => G.coordinateEdgeEnergyDensity φ d z.val)
    (fun d => (G.coordinateEdgeEnergyDensity_endpoints φ d).1)
    (fun d => (G.coordinateEdgeEnergyDensity_endpoints φ d).2) e x

theorem MetricGraph.coordinateEnergyDensity_nonneg (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (p : GraphRealization G) :
    0 ≤ G.coordinateEnergyDensity φ p := by
  obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective p
  rw [G.coordinateEnergyDensity_edge]
  exact div_nonneg (sq_nonneg _) (G.conductance_pos e x.val x.property).le

end TimeTraps.Graph
