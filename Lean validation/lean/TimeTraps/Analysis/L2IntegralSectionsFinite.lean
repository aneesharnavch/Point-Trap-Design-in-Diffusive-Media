module

public import TimeTraps.Analysis.L2IntegralSections
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-! For a finite sample measure, integrability of a family in L²
controls the product L¹ norm of any jointly measurable representatives.
Measurable-event indicator tests then identify the ordinary section
integral with the L²-valued Bochner integral. No pointwise bound on the
sections is required. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter Set
open scoped ENNReal

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
variable {μ : Measure α} {P : Measure Ω}

theorem real_L2_integral_norm_le [IsFiniteMeasure P] (u : Lp ℝ 2 P) :
    (∫ ω, ‖u ω‖ ∂P) ≤ ‖u‖ * Real.sqrt (P.real univ) := by
  have hs := memLp_integral_mul_sq_le (Lp.memLp u).norm
    (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P)
  have hu : ‖u‖ ^ 2 = ∫ ω, u ω ^ 2 ∂P := by
    simpa only [Lp.toLp_coeFn] using memLp_norm_toLp_sq (Lp.memLp u)
  have hs' : (∫ ω, ‖u ω‖ ∂P) ^ 2 ≤ ‖u‖ ^ 2 * P.real univ := by
    simpa only [mul_one, Real.norm_eq_abs, sq_abs, one_pow, integral_const, smul_eq_mul,
      mul_one, ← hu] using hs
  apply (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  calc
    _ ≤ ‖u‖ ^ 2 * P.real univ := hs'
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ P.real univ)]

theorem real_L2_sections_integrable [SFinite μ] [IsFiniteMeasure P]
    {F : α → Lp ℝ 2 P} (hF : Integrable F μ)
    {f : α × Ω → ℝ} (hf : AEStronglyMeasurable f (μ.prod P))
    (hcoe : ∀ a, F a =ᵐ[P] (fun ω => f (a, ω))) : Integrable f (μ.prod P) := by
  apply (integrable_prod_iff hf).mpr
  constructor
  · exact Eventually.of_forall (fun a => ((Lp.memLp (F a)).integrable (by norm_num)).congr (hcoe a))
  · apply (hF.norm.mul_const (Real.sqrt (P.real univ))).mono' hf.norm.integral_prod_right'
    filter_upwards [] with a
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    calc
      _ = ∫ ω, ‖F a ω‖ ∂P := integral_congr_ae ((hcoe a).symm.fun_comp norm)
      _ ≤ _ := real_L2_integral_norm_le (F a)

theorem real_L2_integral_sections_ae [SFinite μ] [IsFiniteMeasure P]
    {F : α → Lp ℝ 2 P} (hF : Integrable F μ)
    {f : α × Ω → ℝ} (hf : AEStronglyMeasurable f (μ.prod P))
    (hcoe : ∀ a, F a =ᵐ[P] (fun ω => f (a, ω))) :
    (fun ω => (∫ a, F a ∂μ : Lp ℝ 2 P) ω) =ᵐ[P] (fun ω => ∫ a, f (a, ω) ∂μ) := by
  have hp := real_L2_sections_integrable hF hf hcoe
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp (∫ a, F a ∂μ)).integrable (by norm_num)) hp.integral_prod_right
  intro s hs hPs
  let v : Lp ℝ 2 P := indicatorConstLp 2 hs hPs.ne (1 : ℝ)
  have hpr : Integrable f (μ.prod (P.restrict s)) :=
    hp.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    _ = inner ℝ v (∫ a, F a ∂μ) := (L2.inner_indicatorConstLp_one hs hPs.ne _).symm
    _ = ∫ a, inner ℝ v (F a) ∂μ := (integral_inner hF v).symm
    _ = ∫ a, ∫ ω in s, f (a, ω) ∂P ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [L2.inner_indicatorConstLp_one hs hPs.ne]
      exact setIntegral_congr_ae hs ((hcoe a).mono (fun _ hω _ => hω))
    _ = _ := integral_integral_swap hpr

end TimeTraps.Analysis
