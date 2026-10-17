module

public import TimeTraps.Probability.GraphConservativeOccupationTerminalData
public import TimeTraps.Probability.GraphConservativeOccupationConditionalActual
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! The explicit stopped occupation process is the genuine terminal
conditional-expectation martingale, with no conditional Markov premise. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationTerminalProcess_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (H t : ℝ≥0) :
    (P.continuousPathLaw hκ x)[graphOccupation P.geometry f H |
        graphContinuousNaturalFiltration P.geometry t] =ᵐ[P.continuousPathLaw hκ x]
      P.occupationTerminalProcess f H t := by
  let inst := P.continuousPathLaw_probability hκ x
  rcases le_total t H with htH | hHt
  · change _ =ᵐ[P.continuousPathLaw hκ x] (fun p =>
      graphOccupation P.geometry f (min t H) p +
        P.occupationPotential f (H.val - (min t H).val) (p (min t H)))
    simpa only [min_eq_left htH] using P.occupation_condExp hκ x f htH
  · rw [P.occupationTerminalProcess_of_horizon_le f hHt]
    have hX : StronglyAdapted (graphContinuousNaturalFiltration P.geometry)
        (fun s (p : GraphContinuousPath P.geometry) => p s) := Filtration.stronglyAdapted_natural _
    apply Filter.EventuallyEq.of_eq
    exact condExp_of_stronglyMeasurable (graphContinuousNaturalFiltration P.geometry |>.le t)
      ((P.occupation_prefix_stronglyMeasurable _ hX f H).mono
        ((graphContinuousNaturalFiltration P.geometry).mono hHt))
      (P.occupation_integrable hκ x f H.coe_nonneg)

theorem GraphShiftedContactOperatorProblem.occupationTerminalProcess_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (H t : ℝ≥0) :
    MemLp (P.occupationTerminalProcess f H t) 2 (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  apply MemLp.of_bound (((P.occupationTerminalProcess_stronglyAdapted f H t).mono
    ((graphContinuousNaturalFiltration P.geometry).le t)).aestronglyMeasurable) (H.val * ‖f‖)
  exact Eventually.of_forall (P.occupationTerminalProcess_norm_le f H t)

theorem GraphShiftedContactOperatorProblem.occupationTerminalProcess_martingale
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (H : ℝ≥0) :
    Martingale (P.occupationTerminalProcess f H) (graphContinuousNaturalFiltration P.geometry)
      (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (martingale_condExp (graphOccupation P.geometry f H)
    (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw hκ x)).congr
      (P.occupationTerminalProcess_stronglyAdapted f H) (P.occupationTerminalProcess_condExp hκ x f H)

end TimeTraps.Analysis
