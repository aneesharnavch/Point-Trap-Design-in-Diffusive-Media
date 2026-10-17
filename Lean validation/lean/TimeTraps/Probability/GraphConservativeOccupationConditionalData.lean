module

public import TimeTraps.Probability.GraphConservativeOccupationPotentialMean
public import TimeTraps.Probability.ConditionalIntegral

@[expose] public section

/-! Continuous elapsed-time conditional sections and their literal
finite-time potential integral for the actual graph semigroup. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_future_section_continuous
    (P : GraphShiftedContactOperatorProblem V E)
    (f : C(GraphRealization P.geometry, ℝ)) (s : ℝ≥0) :
    Continuous (fun q : ℝ × GraphRealization P.geometry =>
      P.realizedFeller (q.1.toNNReal - s) f q.2) := by
  have hc : Continuous (fun q : ℝ × GraphRealization P.geometry =>
      P.realizedFeller (q.1.toNNReal - s) f) := (P.realizedFeller_strong_continuous f).comp
    ((continuous_real_toNNReal.comp continuous_fst).sub continuous_const)
  exact continuous_eval.comp (hc.prodMk continuous_snd)

theorem GraphShiftedContactOperatorProblem.occupation_future_section_integral
    (P : GraphShiftedContactOperatorProblem V E)
    (f : C(GraphRealization P.geometry, ℝ)) {s H : ℝ≥0} (hsH : s ≤ H)
    (y : GraphRealization P.geometry) :
    (∫ r in s.val..H.val, P.realizedFeller (r.toNNReal - s) f y) =
      P.occupationPotential f (H.val - s.val) y := by
  have hi : IntervalIntegrable (fun r : ℝ => P.realizedFeller (r.toNNReal - s) f)
      volume s.val H.val := ((P.realizedFeller_strong_continuous f).comp
        (continuous_real_toNNReal.sub continuous_const)).intervalIntegrable _ _
  have he := P.occupationPotential_translate f (s := s.val) (T := H.val) s.coe_nonneg hsH
  have he' : (∫ r in s.val..H.val, P.realizedFeller (r.toNNReal - s) f) =
      P.occupationPotential f (H.val - s.val) := by
    have hsval : s.val.toNNReal = s := Real.toNNReal_coe
    simpa only [hsval] using he
  exact ((ContinuousMap.evalCLM ℝ y).intervalIntegral_comp_comm hi).trans
    (congrArg (fun u : C(GraphRealization P.geometry, ℝ) => u y) he')

end TimeTraps.Analysis
