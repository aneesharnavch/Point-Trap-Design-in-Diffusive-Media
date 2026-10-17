module

public import TimeTraps.Analysis.GraphConservativeSmoothStep
public import TimeTraps.Analysis.GraphConservativeResistanceCoordinate

@[expose] public section

/-! The original conductance produces a smooth resistance coordinate.
Its flux and generator are explicit continuous functions with zero
endpoint values; no derivative of the conductance is used. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis

variable {V E : Type*}

noncomputable def MetricGraph.smoothResistance (G : MetricGraph V E) (e : E) (x : ℝ) : ℝ :=
  graphSmoothStep (G.normalizedResistance e x)

noncomputable def MetricGraph.smoothResistanceFlux (G : MetricGraph V E) (e : E) (x : ℝ) : ℝ :=
  graphSmoothStepSlope (G.normalizedResistance e x) / G.resistance e

noncomputable def MetricGraph.smoothResistanceGenerator (G : MetricGraph V E) (e : E) (x : ℝ) : ℝ :=
  graphSmoothStepCurvature (G.normalizedResistance e x) /
    (G.conductance e x * G.resistance e ^ 2)

theorem MetricGraph.smoothResistance_continuous (G : MetricGraph V E) (e : E) :
    ContinuousOn (G.smoothResistance e) (Icc (0 : ℝ) (G.length e)) :=
  (by unfold graphSmoothStep; fun_prop : Continuous graphSmoothStep).comp_continuousOn
    (G.normalizedResistance_continuous e)

theorem MetricGraph.smoothResistance_endpoints (G : MetricGraph V E) (e : E) :
    G.smoothResistance e 0 = 0 ∧ G.smoothResistance e (G.length e) = 1 := by
  simp only [smoothResistance, (G.normalizedResistance_endpoints e).1,
    (G.normalizedResistance_endpoints e).2, graphSmoothStep_endpoints.1,
    graphSmoothStep_endpoints.2.1, and_self]

theorem MetricGraph.smoothResistance_strictMonoOn (G : MetricGraph V E) (e : E) :
    StrictMonoOn (G.smoothResistance e) (Icc (0 : ℝ) (G.length e)) := by
  intro x hx y hy hxy
  exact graphSmoothStep_strictMonoOn (G.normalizedResistance_mem e hx)
    (G.normalizedResistance_mem e hy) (G.normalizedResistance_strictMonoOn e hx hy hxy)

theorem MetricGraph.smoothResistance_mem (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (G.length e)) :
    G.smoothResistance e x ∈ Icc (0 : ℝ) 1 :=
  graphSmoothStep_mem (G.normalizedResistance_mem e hx)

theorem MetricGraph.smoothResistance_hasDerivAt (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (G.length e)) :
    HasDerivAt (G.smoothResistance e) (G.smoothResistanceFlux e x / G.conductance e x) x := by
  convert! (graphSmoothStep_hasDerivAt (G.normalizedResistance e x)).comp x
    (G.normalizedResistance_hasDerivAt e hx) using 1
  unfold smoothResistanceFlux
  ring

theorem MetricGraph.smoothResistanceFlux_hasDerivAt (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (G.length e)) :
    HasDerivAt (G.smoothResistanceFlux e) (G.smoothResistanceGenerator e x) x := by
  convert! ((graphSmoothStepSlope_hasDerivAt (G.normalizedResistance e x)).comp x
    (G.normalizedResistance_hasDerivAt e hx)).div_const (G.resistance e) using 1
  unfold smoothResistanceGenerator
  ring

theorem MetricGraph.smoothResistance_flux_generator_continuous (G : MetricGraph V E) (e : E) :
    ContinuousOn (G.smoothResistanceFlux e) (Icc (0 : ℝ) (G.length e)) ∧
      ContinuousOn (G.smoothResistanceGenerator e) (Icc (0 : ℝ) (G.length e)) := by
  constructor
  · exact ((by unfold graphSmoothStepSlope; fun_prop : Continuous graphSmoothStepSlope).comp_continuousOn
      (G.normalizedResistance_continuous e)).div_const (G.resistance e)
  · exact ((by unfold graphSmoothStepCurvature; fun_prop : Continuous graphSmoothStepCurvature).comp_continuousOn
      (G.normalizedResistance_continuous e)).div
        ((G.conductance_continuous e).mul continuousOn_const)
        (fun x hx => mul_ne_zero (G.conductance_pos e x hx).ne' (pow_ne_zero _ (G.resistance_pos e).ne'))

theorem MetricGraph.smoothResistance_flux_generator_endpoints (G : MetricGraph V E) (e : E) :
    G.smoothResistanceFlux e 0 = 0 ∧ G.smoothResistanceFlux e (G.length e) = 0 ∧
      G.smoothResistanceGenerator e 0 = 0 ∧ G.smoothResistanceGenerator e (G.length e) = 0 := by
  simp only [smoothResistanceFlux, smoothResistanceGenerator,
    (G.normalizedResistance_endpoints e).1, (G.normalizedResistance_endpoints e).2,
    graphSmoothStep_endpoints.2.2.1, graphSmoothStep_endpoints.2.2.2.1,
    graphSmoothStep_endpoints.2.2.2.2.1, graphSmoothStep_endpoints.2.2.2.2.2, zero_div, and_self]

end TimeTraps.Graph
