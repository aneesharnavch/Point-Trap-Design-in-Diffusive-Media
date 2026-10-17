module

public import TimeTraps.Analysis.GraphConservativeVariation
public import TimeTraps.Analysis.GraphShiftedContactFellerConservative
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Order and constant bounds for the actual conservative continuous
graph semigroup. These will be applied to the genuine generator of
squared and fourth-power coordinate increments. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedFeller_mono
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    {f g : C(GraphRealization P.geometry, ℝ)} (hfg : ∀ x, f x ≤ g x)
    (x : GraphRealization P.geometry) : P.realizedFeller t f x ≤ P.realizedFeller t g x := by
  have hn := P.realizedFeller_nonneg t (g - f) (fun y => sub_nonneg.mpr (hfg y)) x
  simpa only [map_sub, ContinuousMap.sub_apply, sub_nonneg] using hn

theorem GraphShiftedContactOperatorProblem.realizedFeller_const
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (t : ℝ≥0) (c : ℝ) :
    P.realizedFeller t (ContinuousMap.const (GraphRealization P.geometry) c) =
      ContinuousMap.const (GraphRealization P.geometry) c := by
  have he : ContinuousMap.const (GraphRealization P.geometry) c =
      c • ContinuousMap.const (GraphRealization P.geometry) (1 : ℝ) := by
    ext x
    exact (mul_one c).symm
  rw [he, map_smul, P.realizedFeller_one hκ]

theorem GraphShiftedContactOperatorProblem.realizedFeller_le_const
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (t : ℝ≥0)
    {f : C(GraphRealization P.geometry, ℝ)} {c : ℝ} (hf : ∀ x, f x ≤ c)
    (x : GraphRealization P.geometry) : P.realizedFeller t f x ≤ c := by
  have he := P.realizedFeller_mono t (g := ContinuousMap.const _ c) hf x
  rw [P.realizedFeller_const hκ] at he
  exact he

theorem GraphShiftedContactOperatorProblem.realizedFeller_observation_continuous
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (x : GraphRealization P.geometry) :
    Continuous (fun s : ℝ => P.realizedFeller s.toNNReal f x) :=
  (continuous_eval_const x).comp ((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal)

end TimeTraps.Analysis
