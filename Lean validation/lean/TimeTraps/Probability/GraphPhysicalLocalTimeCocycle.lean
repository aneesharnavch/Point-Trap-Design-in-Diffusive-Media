module

public import TimeTraps.Probability.GraphPhysicalLocalTimePath
public import TimeTraps.Probability.GraphPhysicalClockCocycle
public import TimeTraps.Probability.GraphPointLocalTimeCocycle

@[expose] public section

/-! The actual physical local-time cocycle follows from the original
canonical convergence event and the inverse clock cocycle. The shifted
sample is the original trajectory shifted by the inverse physical time. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalLocalTimePath_cocycle
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) {p : GraphContinuousPath P.geometry}
    (hp : GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p) (s t : ℝ≥0) :
    P.physicalLocalTimePath b hb a p (s + t) = P.physicalLocalTimePath b hb a p s +
      P.physicalLocalTimePath b hb a
        (graphContinuousPathShift P.geometry (P.geometry.physicalInverseClock b hb s p) p) t := by
  simp only [P.physicalLocalTimePath_apply, P.geometry.physicalInverseClock_add]
  exact P.pointLocalTimePath_cocycle a hp _ _

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_cocycle
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) {p : GraphContinuousPath P.geometry}
    (hp : GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p) (s t : ℝ≥0) :
    P.physicalLocalTime b hb a (s + t) p = P.physicalLocalTime b hb a s p +
      P.physicalLocalTime b hb a t
        (graphContinuousPathShift P.geometry (P.geometry.physicalInverseClock b hb s p) p) := by
  simp only [P.physicalLocalTime_apply, P.geometry.physicalInverseClock_add]
  exact P.pointLocalTime_cocycle a hp _ _

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_cocycle_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ s t : ℝ≥0,
      P.physicalLocalTime b hb a (s + t) p = P.physicalLocalTime b hb a s p +
        P.physicalLocalTime b hb a t
          (graphContinuousPathShift P.geometry (P.geometry.physicalInverseClock b hb s p) p) :=
  (P.localTimeApproximant_hasLimit_ae hκ x a).mono
    (fun _ hp s t => P.physicalLocalTime_cocycle b hb a hp s t)

end TimeTraps.Analysis
