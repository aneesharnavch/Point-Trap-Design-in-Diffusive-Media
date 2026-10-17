module

public import TimeTraps.Probability.ConditionalIntegral
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Finite-time product integrability of a continuous martingale follows
from its terminal L1 bound. Continuity is required only on one full event;
no completion of the original filtration is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem aeContinuousProcess_jointly_aestronglyMeasurable
    {M : ℝ≥0 → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (M t))
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (ν : Measure ℝ) :
    AEStronglyMeasurable (fun q : ℝ × Ω => M q.1.toNNReal q.2) (ν.prod μ) := by
  classical
  obtain ⟨N, hsub, hNm, hNμ⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  let M' : ℝ → Ω → ℝ := fun t ω => if ω ∈ N then 0 else M t.toNNReal ω
  have hmc : ∀ ω, Continuous (fun t => M' t ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa only [M', if_pos hω] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    · have hh : Continuous (fun t => M t ω) := by
        by_contra hn
        exact hω (hsub hn)
      simpa only [M', if_neg hω, Function.comp_def] using hh.comp continuous_real_toNNReal
  have hmm : ∀ t, StronglyMeasurable (M' t) := by
    intro t
    exact stronglyMeasurable_const.piecewise hNm (hm t.toNNReal)
  have hj := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hmc hmm
  apply hj.aestronglyMeasurable.congr
  have he : ∀ᵐ ω ∂μ, ω ∉ N := compl_mem_ae_iff.mpr hNμ
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae he] with q hq
  change (if q.2 ∈ N then 0 else M q.1.toNNReal q.2) = _
  exact if_neg hq

theorem martingale_exponential_product_integrable {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (s t : ℝ≥0) :
    Integrable (fun q : ℝ × Ω => Real.exp q.1 * M q.1.toNNReal q.2)
      ((volume.restrict (Ioc (s : ℝ) (t : ℝ))).prod μ) := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  have hj := aeContinuousProcess_jointly_aestronglyMeasurable
    (fun r => (hM.stronglyAdapted r).mono (ℱ.le r)) hc ν
  have hw : AEStronglyMeasurable (fun q : ℝ × Ω => Real.exp q.1) (ν.prod μ) :=
    (Real.continuous_exp.stronglyMeasurable.comp_measurable measurable_fst).aestronglyMeasurable
  have hG := hw.mul hj
  apply (integrable_prod_iff hG).mpr
  refine ⟨Eventually.of_forall (fun r => ?_), ?_⟩
  · simpa only [Pi.mul_apply] using (hM.integrable r.toNNReal).const_mul (Real.exp r)
  · apply (integrable_const (Real.exp (t : ℝ) * ∫ ω, ‖M t ω‖ ∂μ)).mono'
      hG.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hr.2
    have hb : (∫ ω, ‖M r.toNNReal ω‖ ∂μ) ≤ ∫ ω, ‖M t ω‖ ∂μ := by
      calc
        _ = ∫ ω, ‖μ[M t | ℱ r.toNNReal] ω‖ ∂μ :=
          integral_congr_ae ((hM.condExp_ae_eq hrt).symm.fun_comp norm)
        _ ≤ _ := integral_norm_condExp_le _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp only [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hr.2) (integral_nonneg (fun _ => norm_nonneg _)))
end TimeTraps.Probability
