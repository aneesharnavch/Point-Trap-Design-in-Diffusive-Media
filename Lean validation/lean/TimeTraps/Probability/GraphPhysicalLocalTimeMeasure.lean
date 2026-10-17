module

public import TimeTraps.Probability.GraphPhysicalLocalTimeSupport
public import TimeTraps.Probability.GraphPointLocalTimeContactMeasure

@[expose] public section

/-! The actual physical local-time measure has exactly the inverse-clock
increments, including their raw all-time version under every start. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_Ioc
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (s t : ℝ≥0) :
    P.physicalLocalTimeMeasure b hb a p (Ioc s.val t.val) =
      ENNReal.ofReal (P.physicalLocalTimePath b hb a p t - P.physicalLocalTimePath b hb a p s) := by
  rw [physicalLocalTimeMeasure, StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (P.physicalLocalTimePath b hb a p t.val.toNNReal -
    P.physicalLocalTimePath b hb a p s.val.toNNReal) = _
  exact congrArg ENNReal.ofReal (congrArg₂ (fun u v : ℝ => u - v)
    (congrArg (P.physicalLocalTimePath b hb a p) (show t.val.toNNReal = t from Real.toNNReal_coe))
    (congrArg (P.physicalLocalTimePath b hb a p) (show s.val.toNNReal = s from Real.toNNReal_coe)))

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_mass
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (T : ℝ≥0) :
    P.physicalLocalTimeMeasure b hb a p (Ioc (0 : ℝ) T.val) = ENNReal.ofReal (P.physicalLocalTimePath b hb a p T) := by
  have h := P.physicalLocalTimeMeasure_Ioc b hb a p 0 T
  change P.physicalLocalTimeMeasure b hb a p (Ioc (0 : ℝ) T.val) =
    ENNReal.ofReal (P.physicalLocalTimePath b hb a p T - P.physicalLocalTimePath b hb a p 0) at h
  rw [P.physicalLocalTimePath_zero, sub_zero] at h
  exact h

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_Ioc_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ s t : ℝ≥0,
      P.physicalLocalTimeMeasure b hb a p (Ioc s.val t.val) =
        ENNReal.ofReal (P.physicalLocalTime b hb a t p - P.physicalLocalTime b hb a s p) := by
  filter_upwards [P.physicalLocalTime_eq_path_ae hκ b hb x a] with p hp s t
  rw [P.physicalLocalTimeMeasure_Ioc, hp s, hp t]

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_inverse_interval
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) (s t : ℝ≥0) :
    P.physicalLocalTimeMeasure b hb a p (Ioc s.val t.val) =
      P.pointLocalTimeMeasure a p
        (Ioc (P.geometry.physicalInverseClock b hb s p).val
          (P.geometry.physicalInverseClock b hb t p).val) := by
  rw [P.physicalLocalTimeMeasure_Ioc, P.pointLocalTimeMeasure_Ioc]
  rfl

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_clock_interval
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) (s t : ℝ≥0) :
    P.physicalLocalTimeMeasure b hb a p
        (Ioc (P.geometry.physicalClock b hb s p).val (P.geometry.physicalClock b hb t p).val) =
      P.pointLocalTimeMeasure a p (Ioc s.val t.val) := by
  rw [P.physicalLocalTimeMeasure_inverse_interval,
    P.geometry.physicalInverseClock_clock, P.geometry.physicalInverseClock_clock]

end TimeTraps.Analysis
