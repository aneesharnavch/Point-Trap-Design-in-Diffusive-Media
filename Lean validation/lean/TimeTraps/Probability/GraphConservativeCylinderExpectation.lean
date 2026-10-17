module

public import TimeTraps.Probability.GraphConservativeMarkovAbsolute

@[expose] public section

/-! Exact expectation of chronological continuous cylinder words under
the original graph path law. Sorted absolute times use their literal
successive differences, retaining repeated observation times. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.markovCylinder_expectation
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (y : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry) :
    (∫ p, graphMarkovCylinder P.geometry w 0 p ∂P.continuousPathLaw h0 y) =
      P.markovCylinderKernel w y := by
  let inst := P.continuousPathLaw_probability h0 y
  have hτ := isStoppingTime_const (graphContinuousNaturalFiltration P.geometry) (0 : ℝ≥0)
  have he := P.markovCylinder_condExp h0 y w hτ
  calc
    _ = ∫ p, P.markovCylinderKernel w (p 0) ∂P.continuousPathLaw h0 y := by
      rw [← integral_condExp hτ.measurableSpace_le]
      exact integral_congr_ae he
    _ = ∫ _, P.markovCylinderKernel w y ∂P.continuousPathLaw h0 y :=
      integral_congr_ae ((P.continuousPathLaw_initial h0 y).mono
        (fun p hp => congrArg (P.markovCylinderKernel w) hp))
    _ = _ := by simp

theorem GraphShiftedContactOperatorProblem.markovSortedCylinder_expectation
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (y : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry)
    (hw : w.Pairwise (fun a b => a.1 ≤ b.1)) :
    (∫ p, graphMarkovAbsoluteCylinder P.geometry w 0 p ∂P.continuousPathLaw h0 y) =
      P.markovCylinderKernel (graphMarkovDurations 0 w) y := by
  calc
    _ = ∫ p, graphMarkovCylinder P.geometry (graphMarkovDurations 0 w) 0 p
        ∂P.continuousPathLaw h0 y := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro p
      simpa only [zero_add] using
        (graphMarkovDurations_cylinder P.geometry w 0 hw (fun _ _ => bot_le) 0 p).symm
    _ = _ := P.markovCylinder_expectation h0 y (graphMarkovDurations 0 w)

end TimeTraps.Analysis
