module

public import TimeTraps.Probability.GraphLocalTimeRadiusMoment
public import TimeTraps.Probability.GraphLocalTimeCanonicalData

@[expose] public section

/-! The actual normalized occupation paths on the one deterministic
radius schedule. These Borel, raw-adapted approximants are fixed without
choosing an initial probability law. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.localTimeApproximant
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) : C(ℝ≥0, ℝ) :=
  ⟨fun t => graphOccupation P.geometry (P.geometry.pointBump a (P.localTimeRadius n)) t p,
    graphOccupation_time_continuous P.geometry _ p⟩

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_apply
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) (t : ℝ≥0) :
    P.localTimeApproximant a n p t = graphOccupation P.geometry
      (P.geometry.pointBump a (P.localTimeRadius n)) t p := rfl

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_measurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ) :
    Measurable (P.localTimeApproximant a n) :=
  graphLocalTimeApproximant_measurable_of_eval _
    (fun t => (graphOccupation_stronglyMeasurable P.geometry _ t).measurable)

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry)
      (fun t p => P.localTimeApproximant a n p t) := by
  intro t
  exact P.occupation_prefix_stronglyMeasurable _ (Filtration.stronglyAdapted_natural _)
    (P.geometry.pointBump a (P.localTimeRadius n)) t

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_compact
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) (T : ℝ≥0) :
    graphLocalTimeCompactRestriction T (P.localTimeApproximant a n p) =
      graphOccupationCompactPath P.geometry (P.geometry.pointBump a (P.localTimeRadius n)) T p := by
  ext t
  rfl

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_zero
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) : P.localTimeApproximant a n p 0 = 0 := by
  simp only [P.localTimeApproximant_apply, graphOccupation, NNReal.coe_zero, intervalIntegral.integral_same]

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) (t : ℝ≥0) : 0 ≤ P.localTimeApproximant a n p t :=
  intervalIntegral.integral_nonneg t.coe_nonneg
    (fun s _ => P.geometry.pointBump_nonneg a (p s.toNNReal) _)

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_monotone
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) : Monotone (P.localTimeApproximant a n p) := by
  intro s t hst
  exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg
    (show (s : ℝ) ≤ t from hst)
    (Filter.Eventually.of_forall (fun r => P.geometry.pointBump_nonneg a (p r.toNNReal) _))
    ((((P.geometry.pointBump a (P.localTimeRadius n)).continuous.comp p.continuous).comp
      continuous_real_toNNReal).intervalIntegrable 0 t)

end TimeTraps.Analysis
