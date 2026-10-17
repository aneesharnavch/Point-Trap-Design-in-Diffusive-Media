module

public import TimeTraps.Probability.BrownianIntegralContinuousGlobal

@[expose] public section

/-! Every fixed compact restriction of the global continuous integral
agrees almost surely, at all times in that interval, with the checked
compact continuous version. Consequently its actual compact supremum is
measurable, square-integrable, and satisfies the constant-four bound. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def brownianIntegralGlobalCompactPath (f : BrownianIntegrand) (T : ℝ≥0) (ω : ℕ → ℝ) :
    C(BrownianCompactTime T, ℝ) :=
  ⟨fun t => brownianIntegralGlobalPath f t.val ω,
    (brownianIntegralGlobalPath_continuous f ω).comp continuous_subtype_val⟩

theorem brownianIntegralGlobalCompactPath_stronglyMeasurable (f : BrownianIntegrand) (T : ℝ≥0) :
    StronglyMeasurable (brownianIntegralGlobalCompactPath f T) :=
  compactPath_stronglyMeasurable _ (fun t => brownianIntegralGlobalPath_measurable f t.val)

theorem brownianIntegralGlobalPath_compact_ae (f : BrownianIntegrand) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
      brownianIntegralGlobalPath f t.val ω = brownianIntegralContinuousPath T f t ω := by
  have ht : ∀ t : BrownianCompactTime T,
      brownianIntegralGlobalPath f t.val =ᵐ[brownianDyadicMeasure] brownianIntegralContinuousPath T f t :=
    fun t => (brownianIntegralGlobalPath_integral_ae f t.val).trans
      (brownianIntegralContinuousPath_integral_ae T f t).symm
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      brownianIntegralGlobalPath f (denseSeq (BrownianCompactTime T) n).val ω =
        brownianIntegralContinuousPath T f (denseSeq (BrownianCompactTime T) n) ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime T) n))
  filter_upwards [hall] with ω hω
  have he := (denseRange_denseSeq (BrownianCompactTime T)).equalizer
    ((brownianIntegralGlobalPath_continuous f ω).comp continuous_subtype_val)
    (brownianIntegralContinuousPath_continuous T f ω) (funext hω)
  exact congrFun he

theorem brownianIntegralGlobalCompactPath_ae (f : BrownianIntegrand) (T : ℝ≥0) :
    brownianIntegralGlobalCompactPath f T =ᵐ[brownianDyadicMeasure] brownianIntegralContinuousL2 T f :=
  (brownianIntegralGlobalPath_compact_ae f T).mono (fun _ hω => ContinuousMap.ext hω)

theorem brownianIntegralGlobalCompactPath_memLp (f : BrownianIntegrand) (T : ℝ≥0) :
    MemLp (brownianIntegralGlobalCompactPath f T) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianIntegralContinuousL2 T f)).ae_eq (brownianIntegralGlobalCompactPath_ae f T).symm

theorem brownianIntegralGlobalPath_sup_eq_norm (f : BrownianIntegrand) (T : ℝ≥0) (ω : ℕ → ℝ) :
    (⨆ t : BrownianCompactTime T, |brownianIntegralGlobalPath f t.val ω|) =
      ‖brownianIntegralGlobalCompactPath f T ω‖ := by
  rw [(brownianIntegralGlobalCompactPath f T ω).norm_eq_iSup_norm]
  simp only [Real.norm_eq_abs]
  rfl

theorem brownianIntegralGlobalPath_sup_measurable (f : BrownianIntegrand) (T : ℝ≥0) :
    Measurable (fun ω => ⨆ t : BrownianCompactTime T, |brownianIntegralGlobalPath f t.val ω|) := by
  simp only [brownianIntegralGlobalPath_sup_eq_norm]
  exact (brownianIntegralGlobalCompactPath_stronglyMeasurable f T).norm.measurable

theorem brownianIntegralGlobalPath_sup_memLp (f : BrownianIntegrand) (T : ℝ≥0) :
    MemLp (fun ω => ⨆ t : BrownianCompactTime T, |brownianIntegralGlobalPath f t.val ω|)
      2 brownianDyadicMeasure := by
  simp only [brownianIntegralGlobalPath_sup_eq_norm]
  exact (brownianIntegralGlobalCompactPath_memLp f T).norm

theorem brownianIntegralGlobalPath_maximal (f : BrownianIntegrand) (T : ℝ≥0) :
    (∫ ω, (⨆ t : BrownianCompactTime T, |brownianIntegralGlobalPath f t.val ω|) ^ 2
      ∂brownianDyadicMeasure) ≤
      4 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T f‖ ^ 2 := by
  have he : (fun ω => (⨆ t : BrownianCompactTime T, |brownianIntegralGlobalPath f t.val ω|) ^ 2) =ᵐ[brownianDyadicMeasure]
      (fun ω => (⨆ t : BrownianCompactTime T, |brownianIntegralContinuousPath T f t ω|) ^ 2) := by
    filter_upwards [brownianIntegralGlobalPath_compact_ae f T] with ω hω
    simp only [hω]
  rw [integral_congr_ae he]
  exact brownianIntegralContinuousPath_maximal T f

end TimeTraps.Probability

end
