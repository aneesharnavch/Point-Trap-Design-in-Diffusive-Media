module

public import TimeTraps.Probability.GraphPhysicalClockFiltration
public import TimeTraps.Probability.GraphPointLocalTimePath

@[expose] public section

/-! The physical point local time is the original normalized graph point
local time sampled at the actual inverse clock, on the original sample
space. Raw adaptation follows from stopped continuous approximants. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.physicalLocalTime
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  P.pointLocalTime a (P.geometry.physicalInverseClock b hb t p) p

noncomputable def GraphShiftedContactOperatorProblem.physicalLocalTimePath
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) : C(ℝ≥0, ℝ) :=
  ⟨fun t => P.pointLocalTimePath a p (P.geometry.physicalInverseClock b hb t p),
    (P.pointLocalTimePath a p).continuous.comp
      (P.geometry.physicalClockSpeed b hb p).inverse_continuous⟩

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_apply
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    P.physicalLocalTime b hb a t p =
      P.pointLocalTime a (P.geometry.physicalInverseClock b hb t p) p := rfl

theorem GraphShiftedContactOperatorProblem.physicalLocalTimePath_apply
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    P.physicalLocalTimePath b hb a p t =
      P.pointLocalTimePath a p (P.geometry.physicalInverseClock b hb t p) := rfl

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) :
    StronglyAdapted (P.geometry.physicalFiltration b hb) (P.physicalLocalTime b hb a) := by
  intro t
  have hm : Measurable[P.geometry.physicalFiltration b hb t]
      (P.physicalLocalTime b hb a t) := by
    let : MeasurableSpace (GraphContinuousPath P.geometry) := P.geometry.physicalFiltration b hb t
    change Measurable (graphLocalTimeScalarLimit (fun n p =>
      P.localTimeApproximant a n p (P.geometry.physicalInverseClock b hb t p)))
    apply graphLocalTimeScalarLimit_measurable
    intro n
    exact (continuousObservation_stopped_stronglyMeasurable
      (fun s p => P.localTimeApproximant a n p s)
      (P.localTimeApproximant_stronglyAdapted a n)
      (fun p => (P.localTimeApproximant a n p).continuous)
      (P.geometry.physicalInverseClock_isStoppingTime b hb t)).measurable
  exact hm.stronglyMeasurable

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) :
    Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry => P.physicalLocalTime b hb a q.1 q.2) := by
  change Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry =>
    P.pointLocalTime a (P.geometry.physicalInverseClock b hb q.1 q.2) q.2)
  have hi : Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry =>
      (P.geometry.physicalInverseClock b hb q.1 q.2, q.2)) :=
    (P.geometry.physicalInverseClock_jointlyMeasurable b hb).prodMk measurable_snd
  have he := (P.pointLocalTime_jointlyMeasurable a).comp hi
  exact he

theorem GraphShiftedContactOperatorProblem.physicalLocalTimePath_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) :
    Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry => P.physicalLocalTimePath b hb a q.2 q.1) := by
  change Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry =>
    P.pointLocalTimePath a q.2 (P.geometry.physicalInverseClock b hb q.1 q.2))
  have hi : Measurable (fun q : ℝ≥0 × GraphContinuousPath P.geometry =>
      (P.geometry.physicalInverseClock b hb q.1 q.2, q.2)) :=
    (P.geometry.physicalInverseClock_jointlyMeasurable b hb).prodMk measurable_snd
  have he := (P.pointLocalTimePath_jointlyMeasurable a).comp hi
  exact he

end TimeTraps.Analysis
