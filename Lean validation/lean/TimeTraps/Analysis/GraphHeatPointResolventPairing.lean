module

public import TimeTraps.Analysis.GraphHeatPointResolventWeak
public import TimeTraps.Analysis.GraphConservativeVariationIntertwining

@[expose] public section

/-! The point-source weak resolvent tested against continuous sources,
with the pairing taken against the actual ordinary graph length measure. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [Nonempty E] in
theorem graphConservativeContinuousStateL_pairing (G : MetricGraph V E)
    (f g : C(GraphRealization G, ℝ)) :
    inner ℝ (graphConservativeContinuousStateL G f) (graphConservativeContinuousStateL G g) =
      ∫ x, f x * g x ∂G.lengthMeasure := by
  rw [graphL2Product_inner, G.lengthMeasure_integral (fun x => f x * g x) (f.continuous.mul g.continuous)]
  apply Finset.sum_congr rfl
  intro e _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [graphConservativeContinuousStateL_coe G f e,
    graphConservativeContinuousStateL_coe G g e] with x hf hg
  simp only [Real.inner_apply, hf, hg]

theorem GraphShiftedContactOperatorProblem.pointResolventSolution_length_pairing
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (f : C(GraphRealization P.geometry, ℝ)) :
    (∫ x, f x * graphRealizedSobolev P.geometry (P.pointResolventSolution a) x
      ∂P.geometry.lengthMeasure) =
      P.realizedSolutionL (graphConservativeContinuousStateL P.geometry f) a := by
  rw [← graphConservativeContinuousStateL_pairing, graphConservativeContinuousStateL_sobolev,
    P.pointResolventSolution_pairing]

end TimeTraps.Analysis
