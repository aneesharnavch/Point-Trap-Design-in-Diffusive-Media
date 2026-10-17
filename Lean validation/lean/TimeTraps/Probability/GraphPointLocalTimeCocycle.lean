module

public import TimeTraps.Probability.GraphOccupationShift
public import TimeTraps.Probability.GraphPointLocalTimePath

@[expose] public section

/-! The actual graph point local time is additive on its common
convergence event, which is stable under every nonnegative path shift.
The construction uses the literal normalized bumps and the same radius
schedule for all starts, with no Markov premise in the cocycle proof. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_shift
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) (s : ℝ≥0) :
    P.localTimeApproximant a n (graphContinuousPathShift P.geometry s p) =
      continuousPathShift s (P.localTimeApproximant a n p) -
        ContinuousMap.const ℝ≥0 (P.localTimeApproximant a n p s) :=
  graphOccupation_curve_shift P.geometry (P.geometry.pointBump a (P.localTimeRadius n)) p s

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_hasLimit_shift
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    {p : GraphContinuousPath P.geometry} (hp : GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p)
    (s : ℝ≥0) :
    GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) (graphContinuousPathShift P.geometry s p) :=
  hp.shift (graphContinuousPathShift P.geometry) (P.localTimeApproximant_shift a) s

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_shift_eq
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    {p : GraphContinuousPath P.geometry} (hp : GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p)
    (s : ℝ≥0) :
    P.pointLocalTimePath a (graphContinuousPathShift P.geometry s p) =
      continuousPathShift s (P.pointLocalTimePath a p) - ContinuousMap.const ℝ≥0 (P.pointLocalTimePath a p s) :=
  hp.shift_eq (graphContinuousPathShift P.geometry) (P.localTimeApproximant_shift a) s

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_cocycle
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    {p : GraphContinuousPath P.geometry} (hp : GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p)
    (s t : ℝ≥0) :
    P.pointLocalTimePath a p (s + t) = P.pointLocalTimePath a p s +
      P.pointLocalTimePath a (graphContinuousPathShift P.geometry s p) t :=
  hp.cocycle (graphContinuousPathShift P.geometry) (P.localTimeApproximant_shift a) s t

theorem GraphShiftedContactOperatorProblem.pointLocalTime_cocycle
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    {p : GraphContinuousPath P.geometry} (hp : GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p)
    (s t : ℝ≥0) :
    P.pointLocalTime a (s + t) p = P.pointLocalTime a s p +
      P.pointLocalTime a t (graphContinuousPathShift P.geometry s p) :=
  hp.pointwise_cocycle (graphContinuousPathShift P.geometry) (P.localTimeApproximant_shift a) s t

theorem GraphShiftedContactOperatorProblem.pointLocalTime_cocycle_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ s t : ℝ≥0,
      P.pointLocalTime a (s + t) p = P.pointLocalTime a s p +
        P.pointLocalTime a t (graphContinuousPathShift P.geometry s p) :=
  (P.localTimeApproximant_hasLimit_ae hκ x a).mono (fun _ hp s t => P.pointLocalTime_cocycle a hp s t)

end TimeTraps.Analysis
