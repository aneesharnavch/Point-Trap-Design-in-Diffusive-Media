module

public import TimeTraps.Probability.GraphPhysicalLocalTimePath
public import TimeTraps.Probability.GraphPointLocalTimeSupport

@[expose] public section

/-! The physical canonical local time is locally constant away from
actual physical visits, by continuous inverse-clock transport. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalLocalTimePath_locally_constant
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) (t : ℝ≥0)
    (ht : P.geometry.physicalPath b hb p t ≠ a) :
    ∀ᶠ r in 𝓝 t, P.physicalLocalTimePath b hb a p r = P.physicalLocalTimePath b hb a p t :=
  (P.geometry.physicalClockSpeed b hb p).inverse_continuous.continuousAt.tendsto.eventually
    (P.pointLocalTimePath_locally_constant a p (P.geometry.physicalInverseClock b hb t p) ht)

noncomputable def GraphShiftedContactOperatorProblem.physicalLocalTimeStieltjes
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) : StieltjesFunction ℝ :=
  continuousStieltjesFunction (fun t => P.physicalLocalTimePath b hb a p t.toNNReal)
    ((P.physicalLocalTimePath_monotone b hb a p).comp Real.toNNReal_monotone)
    ((P.physicalLocalTimePath b hb a p).continuous.comp continuous_real_toNNReal)

noncomputable def GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) : Measure ℝ :=
  (P.physicalLocalTimeStieltjes b hb a p).measure

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_singleton
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) (t : ℝ) :
    P.physicalLocalTimeMeasure b hb a p {t} = 0 :=
  continuousStieltjesFunction_measure_singleton _ _ _ t

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_support
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : GraphRealization P.geometry) (p : GraphContinuousPath P.geometry) :
    (P.physicalLocalTimeMeasure b hb a p).support ⊆
      {t : ℝ | 0 ≤ t ∧ P.geometry.physicalPath b hb p t.toNNReal = a} := by
  intro t ht
  have ht0 : 0 ≤ t := by
    by_contra hn
    have hn' : t < 0 := lt_of_not_ge hn
    have hf : ∀ᶠ r in 𝓝 t, P.physicalLocalTimePath b hb a p r.toNNReal =
        P.physicalLocalTimePath b hb a p t.toNNReal := by
      filter_upwards [Iio_mem_nhds hn'] with r hr
      rw [Real.toNNReal_of_nonpos (show r ≤ 0 from (show r < 0 from hr).le),
        Real.toNNReal_of_nonpos hn'.le]
    exact (continuousStieltjesFunction_notMem_support _ _ _ t hf) ht
  refine ⟨ht0, ?_⟩
  by_contra hn
  have hf := continuous_real_toNNReal.continuousAt.tendsto.eventually
    (P.physicalLocalTimePath_locally_constant b hb a p t.toNNReal hn)
  exact (continuousStieltjesFunction_notMem_support _ _ _ t hf) ht

end TimeTraps.Analysis
