module

public import TimeTraps.Probability.GraphPhysicalClockReversibility
public import TimeTraps.Probability.GraphPhysicalTransitionClockPairing
public import TimeTraps.Probability.GraphPhysicalTransitionReversibility

@[expose] public section

/-! The original variable-speed graph diffusion is reversible for the
physical rho-weighted measure. Every premise of the clock-correlation,
Laplace uniqueness and Borel-kernel criteria is discharged by the actual
constructed process and its original conservative graph heat law. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) (t : ℝ≥0) :
    P.physicalTransitionPairing h0 b hb f g t = P.physicalTransitionPairing h0 b hb g f t := by
  have he := P.physicalTransitionPairing_eq_of_clock_symmetry h0 b hb f g
    (fun α hα r => P.physicalClockLaplaceIntegrand_symmetric h0 b hb hα.le f g r)
  exact congrFun he t

theorem GraphShiftedContactOperatorProblem.physicalTransition_reversible
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) :
    (P.physicalTransition h0 b hb t).IsReversible P.geometry.physicalSpeedMeasure :=
  P.physicalTransition_reversible_of_pairing h0 b hb t
    (fun f g => P.physicalTransitionPairing_symmetric h0 b hb f g t)

theorem GraphShiftedContactOperatorProblem.physicalTransition_joint_swap
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) :
    (P.geometry.physicalSpeedMeasure ⊗ₘ P.physicalTransition h0 b hb t).map Prod.swap =
      P.geometry.physicalSpeedMeasure ⊗ₘ P.physicalTransition h0 b hb t :=
  P.physicalTransition_joint_swap_of_pairing h0 b hb t
    (fun f g => P.physicalTransitionPairing_symmetric h0 b hb f g t)

theorem GraphShiftedContactOperatorProblem.physicalTransition_invariant
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) :
    (P.physicalTransition h0 b hb t).Invariant P.geometry.physicalSpeedMeasure :=
  (P.physicalTransition_reversible h0 b hb t).invariant

end TimeTraps.Analysis
