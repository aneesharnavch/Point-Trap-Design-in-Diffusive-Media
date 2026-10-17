module

public import TimeTraps.Analysis.GraphConservativeCoordinateDerivatives

@[expose] public section

/-! Every scalar linear coordinate of the actual resistance embedding
has its literal continuous divergence-form flux and generator. The
physical coefficient is never differentiated. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def MetricGraph.coordinateEdgeValue (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) (x : ℝ) : ℝ :=
  φ (G.edgeCoordinates e (G.smoothResistance e x))

noncomputable def MetricGraph.coordinateEdgeFlux (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) (x : ℝ) : ℝ :=
  φ (G.edgeCoordinateSlope e (G.smoothResistance e x)) * G.smoothResistanceFlux e x

noncomputable def MetricGraph.coordinateEdgeGenerator (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) (x : ℝ) : ℝ :=
  φ (G.edgeCoordinateCurvature e (G.smoothResistance e x)) * G.smoothResistanceFlux e x ^ 2 /
    G.conductance e x +
      φ (G.edgeCoordinateSlope e (G.smoothResistance e x)) * G.smoothResistanceGenerator e x

omit [Fintype V] [Fintype E] in
theorem MetricGraph.coordinateEdgeValue_continuous (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) :
    ContinuousOn (G.coordinateEdgeValue φ e) (Icc (0 : ℝ) (G.length e)) :=
  (φ.continuous.comp (G.edgeCoordinates_continuous e)).comp_continuousOn
    (G.smoothResistance_continuous e)

theorem MetricGraph.coordinateEdgeFlux_continuous (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) :
    ContinuousOn (G.coordinateEdgeFlux φ e) (Icc (0 : ℝ) (G.length e)) := by
  have hs : Continuous (G.edgeCoordinateSlope e) := continuous_iff_continuousAt.mpr
    (fun s => (G.edgeCoordinateSlope_hasDerivAt e s).continuousAt)
  exact ((φ.continuous.comp hs).comp_continuousOn (G.smoothResistance_continuous e)).mul
    (G.smoothResistance_flux_generator_continuous e).1

theorem MetricGraph.coordinateEdgeGenerator_continuous (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) :
    ContinuousOn (G.coordinateEdgeGenerator φ e) (Icc (0 : ℝ) (G.length e)) := by
  classical
  have hs : Continuous (G.edgeCoordinateSlope e) := continuous_iff_continuousAt.mpr
    (fun s => (G.edgeCoordinateSlope_hasDerivAt e s).continuousAt)
  have hc : Continuous (G.edgeCoordinateCurvature e) := by
    unfold edgeCoordinateCurvature
    fun_prop
  exact ((((φ.continuous.comp hc).comp_continuousOn (G.smoothResistance_continuous e)).mul
    ((G.smoothResistance_flux_generator_continuous e).1.pow 2)).div
      (G.conductance_continuous e) (fun x hx => (G.conductance_pos e x hx).ne')).add
        (((φ.continuous.comp hs).comp_continuousOn (G.smoothResistance_continuous e)).mul
          (G.smoothResistance_flux_generator_continuous e).2)

theorem MetricGraph.coordinateEdgeValue_hasDerivAt (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (G.length e)) :
    HasDerivAt (G.coordinateEdgeValue φ e) (G.coordinateEdgeFlux φ e x / G.conductance e x) x := by
  have h := (φ.hasFDerivAt.comp_hasDerivAt (G.smoothResistance e x)
    (G.edgeCoordinates_hasDerivAt e (G.smoothResistance e x))).comp x
      (G.smoothResistance_hasDerivAt e hx)
  convert! h using 1
  unfold coordinateEdgeFlux
  ring

theorem MetricGraph.coordinateEdgeFlux_hasDerivAt (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (G.length e)) :
    HasDerivAt (G.coordinateEdgeFlux φ e) (G.coordinateEdgeGenerator φ e x) x := by
  have h := ((φ.hasFDerivAt.comp_hasDerivAt (G.smoothResistance e x)
    (G.edgeCoordinateSlope_hasDerivAt e (G.smoothResistance e x))).comp x
      (G.smoothResistance_hasDerivAt e hx)).mul (G.smoothResistanceFlux_hasDerivAt e hx)
  convert! h using 1
  unfold coordinateEdgeGenerator
  dsimp
  ring

omit [Fintype V] [Fintype E] in
theorem MetricGraph.coordinateEdgeFlux_generator_endpoints (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (e : E) :
    G.coordinateEdgeFlux φ e 0 = 0 ∧ G.coordinateEdgeFlux φ e (G.length e) = 0 ∧
      G.coordinateEdgeGenerator φ e 0 = 0 ∧ G.coordinateEdgeGenerator φ e (G.length e) = 0 := by
  obtain ⟨hl, hr, gl, gr⟩ := G.smoothResistance_flux_generator_endpoints e
  simp only [coordinateEdgeFlux, coordinateEdgeGenerator, hl, hr, gl, gr,
    mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, add_zero, and_self]

end TimeTraps.Graph
