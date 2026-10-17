module

public import TimeTraps.Probability.GraphPointLocalTimeSupport

@[expose] public section

/-! The genuine atomless time measure of the canonical graph local time.
Its mass is the local-time increment and its support consists only of
nonnegative contact times, for every sample path. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeStieltjes
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) : StieltjesFunction ℝ :=
  continuousStieltjesFunction (fun t => P.pointLocalTimePath a p t.toNNReal)
    ((P.pointLocalTimePath_monotone a p).comp Real.toNNReal_monotone)
    ((P.pointLocalTimePath a p).continuous.comp continuous_real_toNNReal)

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeMeasure
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) : Measure ℝ :=
  (P.pointLocalTimeStieltjes a p).measure

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_Ioc
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (s t : ℝ≥0) :
    P.pointLocalTimeMeasure a p (Ioc s.val t.val) =
      ENNReal.ofReal (P.pointLocalTimePath a p t - P.pointLocalTimePath a p s) := by
  rw [pointLocalTimeMeasure, StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (P.pointLocalTimePath a p t.val.toNNReal -
    P.pointLocalTimePath a p s.val.toNNReal) = _
  exact congrArg ENNReal.ofReal (congrArg₂ (fun u v : ℝ => u - v)
    (congrArg (P.pointLocalTimePath a p) (show t.val.toNNReal = t from Real.toNNReal_coe))
    (congrArg (P.pointLocalTimePath a p) (show s.val.toNNReal = s from Real.toNNReal_coe)))

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_singleton
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (t : ℝ) : P.pointLocalTimeMeasure a p {t} = 0 :=
  continuousStieltjesFunction_measure_singleton _ _ _ t

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_support
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) :
    (P.pointLocalTimeMeasure a p).support ⊆ {t : ℝ | 0 ≤ t ∧ p t.toNNReal = a} := by
  intro t ht
  have ht0 : 0 ≤ t := by
    by_contra hn
    have hn' : t < 0 := lt_of_not_ge hn
    have hf : ∀ᶠ r in 𝓝 t, P.pointLocalTimePath a p r.toNNReal = P.pointLocalTimePath a p t.toNNReal := by
      filter_upwards [Iio_mem_nhds hn'] with r hr
      rw [Real.toNNReal_of_nonpos (show r ≤ 0 from (show r < 0 from hr).le),
        Real.toNNReal_of_nonpos hn'.le]
    exact (continuousStieltjesFunction_notMem_support _ _ _ t hf) ht
  refine ⟨ht0, ?_⟩
  by_contra hn
  have hf := continuous_real_toNNReal.continuousAt.tendsto.eventually
    (P.pointLocalTimePath_locally_constant a p t.toNNReal hn)
  exact (continuousStieltjesFunction_notMem_support _ _ _ t hf) ht

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_mass
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (T : ℝ≥0) :
    P.pointLocalTimeMeasure a p (Ioc (0 : ℝ) T.val) = ENNReal.ofReal (P.pointLocalTimePath a p T) := by
  have h := P.pointLocalTimeMeasure_Ioc a p 0 T
  change P.pointLocalTimeMeasure a p (Ioc (0 : ℝ) T.val) =
    ENNReal.ofReal (P.pointLocalTimePath a p T - P.pointLocalTimePath a p 0) at h
  rw [P.pointLocalTimePath_zero, sub_zero] at h
  exact h

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_Ioc_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ s t : ℝ≥0,
      P.pointLocalTimeMeasure a p (Ioc s.val t.val) =
        ENNReal.ofReal (P.pointLocalTime a t p - P.pointLocalTime a s p) := by
  filter_upwards [P.pointLocalTime_eq_path_ae hκ x a] with p hp s t
  rw [P.pointLocalTimeMeasure_Ioc, hp s, hp t]

end TimeTraps.Analysis
