module

public import TimeTraps.Analysis.IntegralCauchySchwarz
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Identification of a Bochner integral of actual L2 classes with
the ordinary integrals of jointly measurable sections. The proof uses
Hilbert duality and a proved Fubini domination, not point evaluation as
a continuous functional on L2. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
variable {μ : Measure α} {P : Measure Ω}

theorem real_L2_inner_eq_integral_mul (u v : Lp ℝ 2 P) :
    inner ℝ u v = ∫ ω, u ω * v ω ∂P := by
  simpa only [Lp.toLp_coeFn] using memLp_inner_toLp_eq_integral_mul (Lp.memLp u) (Lp.memLp v)

theorem real_L2_integral_eq_sections [SFinite μ] [IsFiniteMeasure P]
    {F : α → Lp ℝ 2 P} (hF : Integrable F μ)
    {f : α × Ω → ℝ} (hf : AEStronglyMeasurable f (μ.prod P))
    (hcoe : ∀ a, F a =ᵐ[P] (fun ω => f (a, ω))) {G : Lp ℝ 2 P}
    (hG : G =ᵐ[P] (fun ω => ∫ a, f (a, ω) ∂μ))
    {b : α → ℝ} (hb : Integrable b μ)
    (hbound : ∀ᵐ p ∂μ.prod P, |f p| ≤ b p.1) :
    (∫ a, F a ∂μ) = G := by
  apply ext_inner_left ℝ
  intro v
  have hv : Integrable (fun ω => v ω) P := (Lp.memLp v).integrable (by norm_num)
  have hp : Integrable (fun p : α × Ω => v p.2 * f p) (μ.prod P) := by
    apply (hb.mul_prod hv.norm).mono'
      ((((Lp.stronglyMeasurable v).comp_measurable measurable_snd).aestronglyMeasurable).mul hf)
    filter_upwards [hbound] with p hp
    change |v p.2 * f p| ≤ b p.1 * ‖v p.2‖
    rw [abs_mul, Real.norm_eq_abs, mul_comm (b p.1)]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  calc
    _ = ∫ a, inner ℝ v (F a) ∂μ := (integral_inner hF v).symm
    _ = ∫ a, ∫ ω, v ω * f (a, ω) ∂P ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [real_L2_inner_eq_integral_mul]
      apply integral_congr_ae
      filter_upwards [hcoe a] with ω hω
      rw [hω]
    _ = ∫ ω, ∫ a, v ω * f (a, ω) ∂μ ∂P := integral_integral_swap hp
    _ = ∫ ω, v ω * (∫ a, f (a, ω) ∂μ) ∂P := by simp only [integral_const_mul]
    _ = inner ℝ v G := by
      rw [real_L2_inner_eq_integral_mul]
      apply integral_congr_ae
      filter_upwards [hG] with ω hω
      rw [hω]

end TimeTraps.Analysis
