module

public import TimeTraps.Probability.GraphPhysicalLocalTimeData

@[expose] public section

/-! One all-time event identifies the raw physical local time with its
continuous increasing path. Inverse-clock sampling uses that event and
does not substitute a random time into separate fixed-time null sets. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalLocalTimePath_zero
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) :
    P.physicalLocalTimePath b hb a p 0 = 0 := by
  change P.pointLocalTimePath a p ((P.geometry.physicalClockSpeed b hb p).inverse 0) = 0
  rw [(P.geometry.physicalClockSpeed b hb p).inverse_zero, P.pointLocalTimePath_zero]

theorem GraphShiftedContactOperatorProblem.physicalLocalTimePath_monotone
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) :
    Monotone (P.physicalLocalTimePath b hb a p) :=
  (P.pointLocalTimePath_monotone a p).comp
    (P.geometry.physicalClockSpeed b hb p).inverse_strictMono.monotone

theorem GraphShiftedContactOperatorProblem.physicalLocalTimePath_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) (t : ℝ≥0) :
    0 ≤ P.physicalLocalTimePath b hb a p t :=
  P.pointLocalTimePath_nonneg a p _

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_eq_path_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ t,
      P.physicalLocalTime b hb a t p = P.physicalLocalTimePath b hb a p t := by
  filter_upwards [P.pointLocalTime_eq_path_ae hκ x a] with p hp t
  exact hp _

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_regular_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, Continuous (fun t => P.physicalLocalTime b hb a t p) ∧
      Monotone (fun t => P.physicalLocalTime b hb a t p) ∧ P.physicalLocalTime b hb a 0 p = 0 := by
  filter_upwards [P.physicalLocalTime_eq_path_ae hκ b hb x a] with p hp
  simp only [hp]
  exact ⟨(P.physicalLocalTimePath b hb a p).continuous,
    P.physicalLocalTimePath_monotone b hb a p, P.physicalLocalTimePath_zero b hb a p⟩

theorem GraphShiftedContactOperatorProblem.physicalLocalTime_at_clock
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) (t : ℝ≥0) :
    P.physicalLocalTime b hb a (P.geometry.physicalClock b hb t p) p = P.pointLocalTime a t p := by
  rw [P.physicalLocalTime_apply, P.geometry.physicalInverseClock_clock]

end TimeTraps.Analysis
