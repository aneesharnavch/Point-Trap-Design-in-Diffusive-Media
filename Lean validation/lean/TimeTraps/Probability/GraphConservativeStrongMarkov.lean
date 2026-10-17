module

public import TimeTraps.Probability.GraphConservativeStrongMarkovData
public import TimeTraps.Probability.ContinuousObservationStoppingLimit

@[expose] public section

/-! Strong Markov state observations for the actual conservative graph
path law. Every finite-valued stopping time is covered, and hence every
bounded stopping time. No strong-Markov premise is imposed on the law. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_strongMarkov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (h : ℝ≥0)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry)
      (fun p => (τ p : WithTop ℝ≥0))) :
    (P.continuousPathLaw hκ x)[fun p : GraphContinuousPath P.geometry => f (p (τ p + h)) |
        hτ.measurableSpace] =ᵐ[P.continuousPathLaw hκ x]
      fun p => P.realizedFeller h f (p (τ p)) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact continuousObservation_stopping_condExp (P.continuousPathLaw hκ x)
    (fun t (p : GraphContinuousPath P.geometry) => f (p t))
    (fun t (p : GraphContinuousPath P.geometry) => P.realizedFeller h f (p t))
    (graphObservation_stronglyAdapted P.geometry f)
    (graphObservation_stronglyAdapted P.geometry (P.realizedFeller h f))
    (fun p => f.continuous.comp p.continuous)
    (fun p => (P.realizedFeller h f).continuous.comp p.continuous)
    (fun _ p => f.norm_coe_le_norm _) (fun _ p => (P.realizedFeller h f).norm_coe_le_norm _)
    h (fun s _ hA => P.continuousPathLaw_transition_setIntegral hκ x f s h hA) hτ

end TimeTraps.Analysis
