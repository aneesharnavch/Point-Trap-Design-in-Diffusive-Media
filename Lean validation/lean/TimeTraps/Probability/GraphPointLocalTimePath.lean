module

public import TimeTraps.Probability.GraphPointLocalTimeConvergence
public import TimeTraps.Probability.GraphLocalTimeCanonicalPointwise

@[expose] public section

/-! One graph local-time path functional is defined before the initial
law is chosen. Its same-time scalar version is raw adapted and jointly
measurable, and agrees at every time with the continuous increasing
canonical path on one event of probability one for each initial state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_measurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) :
    Measurable (P.pointLocalTimePath a) :=
  graphLocalTimeCanonicalPath_measurable _ (P.localTimeApproximant_measurable a)

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) :
    Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry => P.pointLocalTimePath a q.2 q.1) :=
  graphLocalTimeCanonicalPath_jointlyMeasurable _ (P.localTimeApproximant_measurable a)

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_zero
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) : P.pointLocalTimePath a p 0 = 0 :=
  graphLocalTimeCanonicalPath_zero _ p (fun n => P.localTimeApproximant_zero a n p)

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_monotone
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) : Monotone (P.pointLocalTimePath a p) :=
  graphLocalTimeCanonicalPath_monotone _ p (fun n => P.localTimeApproximant_monotone a n p)

theorem GraphShiftedContactOperatorProblem.pointLocalTimePath_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (t : ℝ≥0) : 0 ≤ P.pointLocalTimePath a p t :=
  graphLocalTimeCanonicalPath_nonneg _ p (fun n s => P.localTimeApproximant_nonneg a n p s) t

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTime
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  graphLocalTimePointwisePath (P.localTimeApproximant a) t p

theorem GraphShiftedContactOperatorProblem.pointLocalTime_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.pointLocalTime a) :=
  graphLocalTimePointwisePath_stronglyAdapted _ _ (P.localTimeApproximant_stronglyAdapted a)

theorem GraphShiftedContactOperatorProblem.pointLocalTime_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) :
    Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry => P.pointLocalTime a q.1 q.2) :=
  graphLocalTimePointwisePath_jointlyMeasurable _ (P.localTimeApproximant_measurable a)

theorem GraphShiftedContactOperatorProblem.pointLocalTime_eq_path_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ t, P.pointLocalTime a t p = P.pointLocalTimePath a p t :=
  graphLocalTimePointwisePath_indistinguishable _ _ (P.localTimeApproximant_hasLimit_ae hκ x a)

theorem GraphShiftedContactOperatorProblem.pointLocalTime_regular_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, Continuous (fun t => P.pointLocalTime a t p) ∧
      Monotone (fun t => P.pointLocalTime a t p) ∧ P.pointLocalTime a 0 p = 0 := by
  filter_upwards [P.pointLocalTime_eq_path_ae hκ x a] with p hp
  simp only [hp]
  exact ⟨(P.pointLocalTimePath a p).continuous, P.pointLocalTimePath_monotone a p, P.pointLocalTimePath_zero a p⟩

end TimeTraps.Analysis
