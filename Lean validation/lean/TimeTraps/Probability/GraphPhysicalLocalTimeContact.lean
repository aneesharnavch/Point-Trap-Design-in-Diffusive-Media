module

public import TimeTraps.Probability.GraphPhysicalLocalTimeMeasure

@[expose] public section

/-! Literal integration against the actual physical graph point-local-time
measure. Contact support evaluates every spatial weight at the target,
and continuous time weights are integrable on each compact horizon. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_weight_ae
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (g : GraphRealization P.geometry → ℝ) :
    ∀ᵐ t ∂P.physicalLocalTimeMeasure b hb a p, g (P.geometry.physicalPath b hb p t.toNNReal) = g a := by
  have hs : ∀ᵐ t ∂P.physicalLocalTimeMeasure b hb a p, t ∈ (P.physicalLocalTimeMeasure b hb a p).support :=
    (P.physicalLocalTimeMeasure b hb a p).support_mem_ae
  exact hs.mono (fun _ ht => congrArg g ((P.physicalLocalTimeMeasure_support b hb a p ht).2))

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_continuous_integrable
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (w : ℝ≥0 → ℝ) (hw : Continuous w) (T : ℝ≥0) :
    IntegrableOn (fun t : ℝ => w t.toNNReal) (Ioc (0 : ℝ) T.val) (P.physicalLocalTimeMeasure b hb a p) := by
  change IntegrableOn _ _ (P.physicalLocalTimeStieltjes b hb a p).measure
  exact (hw.comp continuous_real_toNNReal).integrableOn_Ioc

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_weighted_contact
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (w : ℝ≥0 → ℝ) (hw : Continuous w)
    (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun t => w t.toNNReal * g (P.geometry.physicalPath b hb p t.toNNReal))
      (Ioc (0 : ℝ) T.val) (P.physicalLocalTimeMeasure b hb a p) ∧
      (∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal * g (P.geometry.physicalPath b hb p t.toNNReal) ∂P.physicalLocalTimeMeasure b hb a p) =
        g a * ∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal ∂P.physicalLocalTimeMeasure b hb a p := by
  have hi := P.physicalLocalTimeMeasure_continuous_integrable b hb a p w hw T
  have he : (fun t => w t.toNNReal * g (P.geometry.physicalPath b hb p t.toNNReal))
      =ᵐ[(P.physicalLocalTimeMeasure b hb a p).restrict (Ioc (0 : ℝ) T.val)] (fun t => g a * w t.toNNReal) := by
    filter_upwards [ae_restrict_of_ae (P.physicalLocalTimeMeasure_weight_ae b hb a p g)] with t ht
    rw [ht, mul_comm]
  exact ⟨(hi.const_mul (g a)).congr he.symm, (integral_congr_ae he).trans (integral_const_mul _ _)⟩

theorem GraphShiftedContactOperatorProblem.physicalLocalTimeMeasure_contact
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun t => g (P.geometry.physicalPath b hb p t.toNNReal)) (Ioc (0 : ℝ) T.val) (P.physicalLocalTimeMeasure b hb a p) ∧
      (∫ t in Ioc (0 : ℝ) T.val, g (P.geometry.physicalPath b hb p t.toNNReal) ∂P.physicalLocalTimeMeasure b hb a p) =
        g a * P.physicalLocalTimePath b hb a p T := by
  have h := P.physicalLocalTimeMeasure_weighted_contact b hb a p (fun _ => 1) continuous_const g T
  simp only [one_mul] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, P.physicalLocalTimeMeasure_mass,
    ENNReal.toReal_ofReal (P.physicalLocalTimePath_nonneg b hb a p T)]

end TimeTraps.Analysis
