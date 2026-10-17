module

public import TimeTraps.Analysis.IntegralCauchySchwarz
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Finite-horizon time integration sends actual product-L² functions
into L² random variables. Its squared bound is the horizon length. -/

namespace TimeTraps.Probability

open MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem brownian_finiteTimeIntegral_bound {μ : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure P] {f : ℝ × Ω → ℝ} (hf : MemLp f 2 (μ.prod P)) :
    (∀ᵐ ω ∂P, MemLp (fun s => f (s, ω)) 2 μ) ∧
    (∀ᵐ ω ∂P, (∫ s, f (s, ω) ∂μ) ^ 2 ≤ μ.real univ * ∫ s, f (s, ω) ^ 2 ∂μ) := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsq := hf.integrable_sq
  have hsections : ∀ᵐ ω ∂P, MemLp (fun s => f (s, ω)) 2 μ := by
    filter_upwards [hi.prod_left_ae, hsq.prod_left_ae] with ω hω hωsq
    exact (memLp_two_iff_integrable_sq hω.aestronglyMeasurable).mpr hωsq
  refine ⟨hsections, ?_⟩
  filter_upwards [hsections] with ω hω
  have hb := TimeTraps.Analysis.memLp_integral_mul_sq_le (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ) hω
  simpa using hb

theorem brownian_finiteTimeIntegral_memLp {μ : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure P] {f : ℝ × Ω → ℝ} (hf : MemLp f 2 (μ.prod P)) :
    MemLp (fun ω => ∫ s, f (s, ω) ∂μ) 2 P := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hm := hi.integral_prod_right.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hf.integrable_sq.integral_prod_right.const_mul (μ.real univ)).mono' (hm.pow 2)
  filter_upwards [(brownian_finiteTimeIntegral_bound hf).2] with ω hω
  change |(∫ s, f (s, ω) ∂μ) ^ 2| ≤ μ.real univ * ∫ s, f (s, ω) ^ 2 ∂μ
  simpa only [abs_sq] using hω

theorem brownian_finiteTimeIntegral_secondMoment {μ : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure P] {f : ℝ × Ω → ℝ} (hf : MemLp f 2 (μ.prod P)) :
    (∫ ω, (∫ s, f (s, ω) ∂μ) ^ 2 ∂P) ≤ μ.real univ * ∫ p, f p ^ 2 ∂μ.prod P := by
  calc
    _ ≤ ∫ ω, μ.real univ * ∫ s, f (s, ω) ^ 2 ∂μ ∂P :=
      integral_mono_ae (brownian_finiteTimeIntegral_memLp hf).integrable_sq
        (hf.integrable_sq.integral_prod_right.const_mul _) (brownian_finiteTimeIntegral_bound hf).2
    _ = _ := by rw [integral_const_mul, ← integral_prod_symm _ hf.integrable_sq]

theorem brownian_timeIntegral_sections [IsFiniteMeasure P]
    {f : ℝ × Ω → ℝ} (hf : MemLp f 2 ((volume : Measure ℝ).prod P)) (T : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun s => f (s, ω)) (Ioc (0 : ℝ) T) := by
  have hr := hf.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl :
    (volume.restrict (Ioc (0 : ℝ) T)).prod P ≤ (volume : Measure ℝ).prod P)
  exact (hr.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_left_ae

theorem brownian_timeIntegral_memLp [IsFiniteMeasure P]
    {f : ℝ × Ω → ℝ} (hf : MemLp f 2 ((volume : Measure ℝ).prod P)) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun ω => ∫ s in (0 : ℝ)..T, f (s, ω)) 2 P := by
  have hr := hf.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl :
    (volume.restrict (Ioc (0 : ℝ) T)).prod P ≤ (volume : Measure ℝ).prod P)
  simpa only [intervalIntegral.integral_of_le hT] using brownian_finiteTimeIntegral_memLp hr

theorem brownian_timeIntegral_secondMoment_le [IsFiniteMeasure P]
    {f : ℝ × Ω → ℝ} (hf : MemLp f 2 ((volume : Measure ℝ).prod P)) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, (∫ s in (0 : ℝ)..T, f (s, ω)) ^ 2 ∂P) ≤
      T * ∫ p, f p ^ 2 ∂(volume : Measure ℝ).prod P := by
  have hle : (volume.restrict (Ioc (0 : ℝ) T)).prod P ≤ (volume : Measure ℝ).prod P :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hr := hf.mono_measure hle
  have hb := brownian_finiteTimeIntegral_secondMoment hr
  have hm : (volume.restrict (Ioc (0 : ℝ) T)).real univ = T := by
    simp [Measure.real, Real.volume_Ioc, hT]
  rw [hm] at hb
  simp_rw [intervalIntegral.integral_of_le hT]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (integral_mono_measure hle (Filter.Eventually.of_forall (fun p => sq_nonneg (f p))) hf.integrable_sq)
    hT)

end TimeTraps.Probability
