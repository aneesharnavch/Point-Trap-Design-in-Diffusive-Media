module

public import TimeTraps.Probability.GraphPointLocalTimeContactMeasure

@[expose] public section

/-! Literal integration against the actual graph point-local-time
measure. Contact support evaluates every spatial weight at the target,
and continuous time weights are integrable on each compact horizon. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_weight_ae
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (g : GraphRealization P.geometry → ℝ) :
    ∀ᵐ t ∂P.pointLocalTimeMeasure a p, g (p t.toNNReal) = g a := by
  have hs : ∀ᵐ t ∂P.pointLocalTimeMeasure a p, t ∈ (P.pointLocalTimeMeasure a p).support :=
    (P.pointLocalTimeMeasure a p).support_mem_ae
  exact hs.mono (fun _ ht => congrArg g ((P.pointLocalTimeMeasure_support a p ht).2))

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_continuous_integrable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (w : ℝ≥0 → ℝ) (hw : Continuous w) (T : ℝ≥0) :
    IntegrableOn (fun t : ℝ => w t.toNNReal) (Ioc (0 : ℝ) T.val) (P.pointLocalTimeMeasure a p) := by
  change IntegrableOn _ _ (P.pointLocalTimeStieltjes a p).measure
  exact (hw.comp continuous_real_toNNReal).integrableOn_Ioc

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_weighted_contact
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (w : ℝ≥0 → ℝ) (hw : Continuous w)
    (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun t => w t.toNNReal * g (p t.toNNReal))
      (Ioc (0 : ℝ) T.val) (P.pointLocalTimeMeasure a p) ∧
      (∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal * g (p t.toNNReal) ∂P.pointLocalTimeMeasure a p) =
        g a * ∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal ∂P.pointLocalTimeMeasure a p := by
  have hi := P.pointLocalTimeMeasure_continuous_integrable a p w hw T
  have he : (fun t => w t.toNNReal * g (p t.toNNReal))
      =ᵐ[(P.pointLocalTimeMeasure a p).restrict (Ioc (0 : ℝ) T.val)] (fun t => g a * w t.toNNReal) := by
    filter_upwards [ae_restrict_of_ae (P.pointLocalTimeMeasure_weight_ae a p g)] with t ht
    rw [ht, mul_comm]
  exact ⟨(hi.const_mul (g a)).congr he.symm, (integral_congr_ae he).trans (integral_const_mul _ _)⟩

theorem GraphShiftedContactOperatorProblem.pointLocalTimeMeasure_contact
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun t => g (p t.toNNReal)) (Ioc (0 : ℝ) T.val) (P.pointLocalTimeMeasure a p) ∧
      (∫ t in Ioc (0 : ℝ) T.val, g (p t.toNNReal) ∂P.pointLocalTimeMeasure a p) =
        g a * P.pointLocalTimePath a p T := by
  have h := P.pointLocalTimeMeasure_weighted_contact a p (fun _ => 1) continuous_const g T
  simp only [one_mul] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, P.pointLocalTimeMeasure_mass,
    ENNReal.toReal_ofReal (P.pointLocalTimePath_nonneg a p T)]

end TimeTraps.Analysis
