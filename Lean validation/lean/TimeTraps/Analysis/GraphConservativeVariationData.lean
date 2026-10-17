module

public import TimeTraps.Analysis.GraphShiftedContactFellerContinuous
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

@[expose] public section

/-! The actual continuous graph functions include continuously into the
ordinary edge-length L2 product. The map retains physical edge values and
agrees with the existing full H1 inclusion. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def graphConservativeContinuousEdgeL (G : MetricGraph V E) (e : E) :
    C(GraphRealization G, ℝ) →L[ℝ] IntervalSobolevL2 0 (G.length e) :=
  (BoundedContinuousFunction.toLp 2 (volume.restrict (Ioo (0 : ℝ) (G.length e))) ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ
      ⟨G.edgePointClamped e, G.edgePointClamped_continuous e⟩).comp
      (ContinuousMap.linearIsometryBoundedOfCompact (GraphRealization G) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

noncomputable def graphConservativeContinuousStateL (G : MetricGraph V E) :
    C(GraphRealization G, ℝ) →L[ℝ] GraphL2Product G :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun e : E => IntervalSobolevL2 0 (G.length e))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun e => graphConservativeContinuousEdgeL G e))

omit [Fintype V] [Nonempty E] in
theorem graphConservativeContinuousStateL_apply (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (e : E) :
    graphConservativeContinuousStateL G f e = graphConservativeContinuousEdgeL G e f := rfl

omit [Fintype V] [Nonempty E] in
theorem graphConservativeContinuousStateL_coe (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (e : E) :
    graphConservativeContinuousStateL G f e =ᵐ[volume.restrict (Ioo (0 : ℝ) (G.length e))]
      fun z => f (G.edgePointClamped e z) :=
  BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict (Ioo (0 : ℝ) (G.length e))) ℝ
    ((ContinuousMap.linearIsometryBoundedOfCompact (GraphRealization G) ℝ ℝ f).compContinuous
      ⟨G.edgePointClamped e, G.edgePointClamped_continuous e⟩)

omit [Fintype V] in
theorem graphConservativeContinuousStateL_sobolev (G : MetricGraph V E)
    (u : GraphSobolevSpace G) :
    graphConservativeContinuousStateL G (graphRealizedSobolev G u) = graphSobolevSpaceStateL G u := by
  apply PiLp.ext
  intro e
  apply Lp.ext
  filter_upwards [graphConservativeContinuousStateL_coe G (graphRealizedSobolev G u) e,
    graphSobolevRepresentative_state_ae G u.val e, ae_restrict_mem measurableSet_Ioo] with z hc hs hz
  rw [hc]
  change graphRealizedSobolev G u (G.edgePoint e (projIcc 0 (G.length e) (G.length_pos e).le z)) = _
  rw [graphRealizedSobolev_edge, projIcc_of_mem (G.length_pos e).le (Ioo_subset_Icc_self hz)]
  exact hs.symm

omit [Fintype V] [Nonempty E] in
theorem graphConservativeContinuousStateL_injective (G : MetricGraph V E) :
    Function.Injective (graphConservativeContinuousStateL G) := by
  intro f g h
  ext p
  obtain ⟨e, z, rfl⟩ := G.edgePoint_surjective p
  have he : (fun x => f (G.edgePointClamped e x)) =ᵐ[volume.restrict (Ioo (0 : ℝ) (G.length e))]
      fun x => g (G.edgePointClamped e x) := by
    filter_upwards [graphConservativeContinuousStateL_coe G f e,
      graphConservativeContinuousStateL_coe G g e] with x hf hg
    rw [← hf, ← hg, h]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he
  have hpoint := Measure.eqOn_Icc_of_ae_eq volume (G.length_pos e).ne he
    (f.continuous.comp (G.edgePointClamped_continuous e)).continuousOn
    (g.continuous.comp (G.edgePointClamped_continuous e)).continuousOn z.property
  simpa only [MetricGraph.edgePointClamped, projIcc_of_mem (G.length_pos e).le z.property] using hpoint

end TimeTraps.Analysis
