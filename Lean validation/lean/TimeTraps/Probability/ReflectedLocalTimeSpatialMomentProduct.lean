module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentLevel
public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-! The square of the actual occupation density is integrable jointly in
level and sample on every finite spatial interval. This justifies the
spatial Cauchy--Schwarz estimate and the subsequent Fubini exchange. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem foldedOccupationDensity_square_product_integrable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x l r : ℝ) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => foldedOccupationDensity L D x T p.2 p.1 ^ 2)
      ((volume.restrict (Ioo l r)).prod brownianDyadicMeasure) := by
  have hm := ((foldedOccupationDensity_timeSlice_jointlyMeasurable L D x T).pow_const 2).aestronglyMeasurable
    (μ := (volume.restrict (Ioo l r)).prod brownianDyadicMeasure)
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall (fun b => (foldedOccupationDensity_level_memLp_all L hL D hD x b T).integrable_sq)
  · apply (integrable_const ((3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2)).mono'
      hm.norm.integral_prod_right'
    filter_upwards [] with b
    simp only [Real.norm_eq_abs, abs_sq]
    rw [abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
    exact foldedOccupationDensity_level_secondMoment_uniform_bound L hL D hD x b T

theorem foldedOccupationDensity_spatial_memLp_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x l r : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, MemLp (foldedOccupationDensity L D x T ω) 2 (volume.restrict (Ioo l r)) := by
  filter_upwards [(foldedOccupationDensity_square_product_integrable L hL D hD x l r T).prod_left_ae] with ω hω
  have hm := (foldedOccupationDensity_timeSlice_jointlyMeasurable L D x T).comp
    (measurable_id.prodMk (measurable_const (a := ω)))
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hω

theorem foldedOccupationDensity_spatial_integral_square_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x l r : ℝ) (hlr : l ≤ r) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      (∫ b in Ioo l r, foldedOccupationDensity L D x T ω b) ^ 2 ≤
        (r - l) * ∫ b in Ioo l r, foldedOccupationDensity L D x T ω b ^ 2 := by
  filter_upwards [foldedOccupationDensity_spatial_memLp_ae L hL D hD x l r T] with ω hω
  have hc := memLp_integral_mul_sq_le hω (memLp_const (μ := volume.restrict (Ioo l r)) (p := 2) (1 : ℝ))
  simpa only [mul_one, one_pow, integral_const, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hlr), smul_eq_mul, mul_one, mul_comm, one_mul] using hc

theorem foldedOccupationDensity_spatial_square_mean_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x l r : ℝ) (hlr : l ≤ r) (T : ℝ≥0) :
    (∫ ω, (∫ b in Ioo l r, foldedOccupationDensity L D x T ω b ^ 2) ∂brownianDyadicMeasure) ≤
      (r - l) * ((3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2) := by
  have hi := foldedOccupationDensity_square_product_integrable L hL D hD x l r T
  rw [← integral_integral_swap hi]
  calc
    _ ≤ ∫ _b in Ioo l r, ((3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2) := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      exact fun b => foldedOccupationDensity_level_secondMoment_uniform_bound L hL D hD x b T
    _ = _ := by rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hlr]

end TimeTraps.Probability
