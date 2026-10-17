module

public import TimeTraps.Analysis.GraphConservativeVariationIntertwining
public import TimeTraps.Analysis.GraphConservativeVariationHeat

@[expose] public section

/-! The actual graph transition satisfies the integrated generator
identity in the uniform norm whenever its original operator has a
continuous representative. No differentiability of conductance or of
the generator representative is required. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedFeller_variation
    (P : GraphShiftedContactOperatorProblem V E) (f g : C(GraphRealization P.geometry, ℝ))
    (hfg : (graphConservativeContinuousStateL P.geometry f,
      graphConservativeContinuousStateL P.geometry g) ∈ P.operator.graph) (T : ℝ≥0) :
    P.realizedFeller T f - f = -∫ s in (0 : ℝ)..T.val, P.realizedFeller s.toNNReal g := by
  let J := graphConservativeContinuousStateL P.geometry
  have hi : IntervalIntegrable (fun s : ℝ => P.realizedFeller s.toNNReal g) volume 0 T.val :=
    ((P.realizedFeller_strong_continuous g).comp continuous_real_toNNReal).intervalIntegrable 0 T.val
  apply graphConservativeContinuousStateL_injective P.geometry
  change J (P.realizedFeller T f - f) = J (-∫ s in (0 : ℝ)..T.val, P.realizedFeller s.toNNReal g)
  calc
    _ = P.heatSemigroup T (J f) - J f := by
      rw [map_sub, P.continuousState_feller]
    _ = -∫ s in (0 : ℝ)..T.val, P.heatSemigroup s.toNNReal (J g) := P.heatSemigroup_variation hfg T
    _ = -∫ s in (0 : ℝ)..T.val, J (P.realizedFeller s.toNNReal g) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      exact (P.continuousState_feller s.toNNReal g).symm
    _ = _ := by rw [J.intervalIntegral_comp_comm hi, map_neg]

theorem GraphShiftedContactOperatorProblem.realizedFeller_diffusion_variation
    (P : GraphShiftedContactOperatorProblem V E) (f g : C(GraphRealization P.geometry, ℝ))
    (hfg : (graphConservativeContinuousStateL P.geometry f,
      -graphConservativeContinuousStateL P.geometry g) ∈ P.operator.graph) (T : ℝ≥0) :
    P.realizedFeller T f - f = ∫ s in (0 : ℝ)..T.val, P.realizedFeller s.toNNReal g := by
  have hh : (graphConservativeContinuousStateL P.geometry f,
      graphConservativeContinuousStateL P.geometry (-g)) ∈ P.operator.graph := by
    simpa only [map_neg] using hfg
  have he := P.realizedFeller_variation f (-g) hh T
  simpa only [map_neg, intervalIntegral.integral_neg, neg_neg] using he

theorem GraphShiftedContactOperatorProblem.realizedFeller_diffusion_variation_apply
    (P : GraphShiftedContactOperatorProblem V E) (f g : C(GraphRealization P.geometry, ℝ))
    (hfg : (graphConservativeContinuousStateL P.geometry f,
      -graphConservativeContinuousStateL P.geometry g) ∈ P.operator.graph) (T : ℝ≥0)
    (x : GraphRealization P.geometry) :
    P.realizedFeller T f x - f x = ∫ s in (0 : ℝ)..T.val, P.realizedFeller s.toNNReal g x := by
  have hi : IntervalIntegrable (fun s : ℝ => P.realizedFeller s.toNNReal g) volume 0 T.val :=
    ((P.realizedFeller_strong_continuous g).comp continuous_real_toNNReal).intervalIntegrable 0 T.val
  have he := congrArg (fun q : C(GraphRealization P.geometry, ℝ) => q x)
    (P.realizedFeller_diffusion_variation f g hfg T)
  exact he.trans ((ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hi).symm

end TimeTraps.Analysis
