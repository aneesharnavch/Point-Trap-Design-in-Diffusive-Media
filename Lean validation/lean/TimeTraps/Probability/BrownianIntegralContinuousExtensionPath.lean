module

public import TimeTraps.Probability.BrownianIntegralContinuousExtension

@[expose] public section

/-! An actual continuous modification on each fixed compact horizon for
every completed integrand. The chosen C-valued representative is jointly
measurable in the ambient sample space. Its raw-filtration measurability
is stated almost everywhere, and the martingale identity is asserted
separately at each fixed time. No global-horizon gluing is asserted. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

def brownianIntegralContinuousPath (T : ℝ≥0) (f : BrownianIntegrand)
    (t : BrownianCompactTime T) (ω : ℕ → ℝ) : ℝ :=
  brownianIntegralContinuousL2 T f ω t

theorem brownianIntegralContinuousPath_continuous (T : ℝ≥0) (f : BrownianIntegrand)
    (ω : ℕ → ℝ) : Continuous (fun t => brownianIntegralContinuousPath T f t ω) :=
  (brownianIntegralContinuousL2 T f ω).continuous

theorem brownianIntegralContinuousPath_stronglyMeasurable (T : ℝ≥0) (f : BrownianIntegrand)
    (t : BrownianCompactTime T) : StronglyMeasurable (brownianIntegralContinuousPath T f t) :=
  (continuous_eval_const t).comp_stronglyMeasurable (Lp.stronglyMeasurable (brownianIntegralContinuousL2 T f))

theorem brownianIntegralContinuousPath_jointlyMeasurable (T : ℝ≥0) (f : BrownianIntegrand) :
    Measurable (fun p : BrownianCompactTime T × (ℕ → ℝ) => brownianIntegralContinuousPath T f p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (brownianIntegralContinuousPath_continuous T f)
    (fun t => (brownianIntegralContinuousPath_stronglyMeasurable T f t).measurable)

theorem brownianIntegralContinuousPath_integral_ae (T : ℝ≥0) (f : BrownianIntegrand)
    (t : BrownianCompactTime T) :
    brownianIntegralContinuousPath T f t =ᵐ[brownianDyadicMeasure]
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val f :=
  brownianIntegralContinuousL2_evaluation_ae T t f

theorem brownianIntegralContinuousPath_martingale_ae (T : ℝ≥0) (f : BrownianIntegrand)
    (t : BrownianCompactTime T) :
    brownianIntegralContinuousPath T f t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess f t.val :=
  (brownianIntegralContinuousPath_integral_ae T f t).trans
    (brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal f t.val).symm

theorem brownianIntegralContinuousPath_raw_aestronglyMeasurable (T : ℝ≥0) (f : BrownianIntegrand)
    (t : BrownianCompactTime T) :
    AEStronglyMeasurable[brownianNaturalFiltration brownianDyadicPath brownianDyadicPath_measurable t.val]
      (brownianIntegralContinuousPath T f t) brownianDyadicMeasure :=
  (brownianIntegralUpTo_aestronglyMeasurable brownianDyadicPath_isPreBrownianReal t.val f).congr
    (brownianIntegralContinuousPath_integral_ae T f t).symm

theorem brownianIntegralContinuousPath_sup_eq_norm (T : ℝ≥0) (f : BrownianIntegrand) (ω : ℕ → ℝ) :
    (⨆ t : BrownianCompactTime T, |brownianIntegralContinuousPath T f t ω|) =
      ‖brownianIntegralContinuousL2 T f ω‖ := by
  rw [(brownianIntegralContinuousL2 T f ω).norm_eq_iSup_norm]
  simp only [Real.norm_eq_abs]
  rfl

theorem brownianIntegralContinuousPath_sup_measurable (T : ℝ≥0) (f : BrownianIntegrand) :
    Measurable (fun ω => ⨆ t : BrownianCompactTime T, |brownianIntegralContinuousPath T f t ω|) := by
  simp only [brownianIntegralContinuousPath_sup_eq_norm]
  exact (Lp.stronglyMeasurable (brownianIntegralContinuousL2 T f)).norm.measurable

theorem brownianIntegralContinuousPath_sup_memLp (T : ℝ≥0) (f : BrownianIntegrand) :
    MemLp (fun ω => ⨆ t : BrownianCompactTime T, |brownianIntegralContinuousPath T f t ω|)
      2 brownianDyadicMeasure := by
  simp only [brownianIntegralContinuousPath_sup_eq_norm]
  exact (Lp.memLp (brownianIntegralContinuousL2 T f)).norm

theorem brownianIntegralContinuousPath_maximal (T : ℝ≥0) (f : BrownianIntegrand) :
    (∫ ω, (⨆ t : BrownianCompactTime T, |brownianIntegralContinuousPath T f t ω|) ^ 2
      ∂brownianDyadicMeasure) ≤
      4 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T f‖ ^ 2 := by
  simp only [brownianIntegralContinuousPath_sup_eq_norm]
  rw [← brownianCompactPathL2_norm_sq]
  have h := (sq_le_sq₀ (norm_nonneg (brownianIntegralContinuousL2 T f))
    (by positivity)).mpr (brownianIntegralContinuousL2_norm_le T f)
  nlinarith

end TimeTraps.Probability

end
