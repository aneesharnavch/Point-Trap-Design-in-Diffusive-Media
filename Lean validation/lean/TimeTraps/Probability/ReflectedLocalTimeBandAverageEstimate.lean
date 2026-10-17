module

public import TimeTraps.Probability.ReflectedLocalTimeBandData

@[expose] public section

/-! An explicit deterministic bound for a normalized band average.
The finite-band constant integral and every required section integral
are included, so this can be applied to the actual occupation density. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem reflectedBandAverage_const (a c : ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ _b in Ioo (a - h) (a + h), c) = (2 * h) * c := by
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith : a - h ≤ a + h)]
  ring

theorem reflectedBandAverage_error_bound (a c s : ℝ) {h : ℝ} (hh : 0 < h)
    {f e : ℝ → ℝ} (hf : IntegrableOn f (Ioo (a - h) (a + h)) volume)
    (he : IntegrableOn e (Ioo (a - h) (a + h)) volume)
    (hb : ∀ᵐ b ∂volume.restrict (Ioo (a - h) (a + h)), |f b - c| ≤ e b / s) :
    |(1 / (2 * h)) * (∫ b in Ioo (a - h) (a + h), f b) - c| ≤
      ((1 / (2 * h)) * ∫ b in Ioo (a - h) (a + h), e b) / s := by
  have hc : IntegrableOn (fun _ : ℝ => c) (Ioo (a - h) (a + h)) volume :=
    (integrableOn_const (C := c) (μ := volume) (s := Icc (a - h) (a + h))
      isCompact_Icc.measure_ne_top).mono_set Ioo_subset_Icc_self
  have hdiv : IntegrableOn (fun b => e b / s) (Ioo (a - h) (a + h)) volume := by
    change Integrable (fun b => e b / s) (volume.restrict (Ioo (a - h) (a + h)))
    simpa only [div_eq_mul_inv] using he.mul_const s⁻¹
  have hi : |∫ b in Ioo (a - h) (a + h), (f b - c)| ≤
      ∫ b in Ioo (a - h) (a + h), e b / s := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le (f := fun b => f b - c) hdiv hb
  have hid : (∫ b in Ioo (a - h) (a + h), e b / s) =
      (∫ b in Ioo (a - h) (a + h), e b) / s := integral_div s _
  have heq : (1 / (2 * h)) * (∫ b in Ioo (a - h) (a + h), f b) - c =
      (1 / (2 * h)) * ∫ b in Ioo (a - h) (a + h), (f b - c) := by
    rw [integral_sub hf hc, reflectedBandAverage_const a c hh]
    field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * h))]
  calc
    _ ≤ (1 / (2 * h)) * ∫ b in Ioo (a - h) (a + h), e b / s :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [hid]; ring

end TimeTraps.Probability
