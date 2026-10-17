module

public import TimeTraps.Probability.GraphPhysicalTransitionKernel
public import TimeTraps.Probability.GraphPhysicalTransitionPairing
public import TimeTraps.Probability.GraphPhysicalReversibilityCriterion

@[expose] public section

/-! Upgrade symmetry of the actual physical continuous-observation
pairings to the full reversible transition measure and invariance of
the original speed measure. The pairing identity is an explicit premise
here, to be discharged by the physical clock and Laplace proof. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalTransition_pairing
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) (f g : GraphRealization P.geometry →ᵇ ℝ) :
    (∫ x, f x * (∫ y, g y ∂P.physicalTransition h0 b hb t x)
      ∂P.geometry.physicalSpeedMeasure) =
        P.physicalTransitionPairing h0 b hb f.toContinuousMap g.toContinuousMap t := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => congrArg (fun z => f x * z)
    (P.physicalTransition_integral h0 b hb t x g.continuous.measurable))

theorem GraphShiftedContactOperatorProblem.physicalTransition_reversible_of_pairing
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0)
    (hs : ∀ f g : C(GraphRealization P.geometry, ℝ),
      P.physicalTransitionPairing h0 b hb f g t = P.physicalTransitionPairing h0 b hb g f t) :
    (P.physicalTransition h0 b hb t).IsReversible P.geometry.physicalSpeedMeasure := by
  apply kernel_reversible_of_pairings
  intro f g
  rw [P.physicalTransition_pairing, P.physicalTransition_pairing]
  exact hs f.toContinuousMap g.toContinuousMap

theorem GraphShiftedContactOperatorProblem.physicalTransition_joint_swap_of_pairing
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0)
    (hs : ∀ f g : C(GraphRealization P.geometry, ℝ),
      P.physicalTransitionPairing h0 b hb f g t = P.physicalTransitionPairing h0 b hb g f t) :
    (P.geometry.physicalSpeedMeasure ⊗ₘ P.physicalTransition h0 b hb t).map Prod.swap =
      P.geometry.physicalSpeedMeasure ⊗ₘ P.physicalTransition h0 b hb t := by
  apply kernel_compProd_swap_of_pairings
  intro f g
  rw [P.physicalTransition_pairing, P.physicalTransition_pairing]
  exact hs f.toContinuousMap g.toContinuousMap

theorem GraphShiftedContactOperatorProblem.physicalTransition_invariant_of_pairing
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0)
    (hs : ∀ f g : C(GraphRealization P.geometry, ℝ),
      P.physicalTransitionPairing h0 b hb f g t = P.physicalTransitionPairing h0 b hb g f t) :
    (P.physicalTransition h0 b hb t).Invariant P.geometry.physicalSpeedMeasure :=
  (P.physicalTransition_reversible_of_pairing h0 b hb t hs).invariant

end TimeTraps.Analysis
