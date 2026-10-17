module

public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorSlope

@[expose] public section

/-! Differentiate the actual heat evolution for every initial vector in the
actual inverse domain.  The derivative is proved on the closed time half-line,
so it includes the right derivative at zero. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.heatCurve_hasDerivWithinAt {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain)
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (h.heatCurve (x : E))
      (-h.heatCurve (inverseOperator T h.injective x) s) (Ici 0) s := by
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_neg_eq_add]
  let L : Filter ℝ := 𝓝[Ici 0 \ {s}] s
  have hp : ∀ i : CompactSpectralIndex T,
      Tendsto (fun t : ℝ =>
        ((slope (fun r : ℝ => Real.exp (-r / i.1)) s t + i.1⁻¹ * Real.exp (-s / i.1)) *
          inner ℝ (h.eigenbasis i) (x : E)) ^ 2) L (𝓝 (0 : ℝ)) := by
    intro i
    have hsl := (compactHeatScalar_hasDerivAt i.1 s).tendsto_slope.mono_left
      (nhdsWithin_mono s (show Ici 0 \ {s} ⊆ {s}ᶜ from fun _ ht => ht.2))
    simpa only [neg_mul, neg_add_cancel, zero_mul, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using
      ((hsl.add_const (i.1⁻¹ * Real.exp (-s / i.1))).mul_const
        (inner ℝ (h.eigenbasis i) (x : E))).pow 2
  have hb : ∀ᶠ t in L, ∀ i : CompactSpectralIndex T,
      ‖((slope (fun r : ℝ => Real.exp (-r / i.1)) s t + i.1⁻¹ * Real.exp (-s / i.1)) *
        inner ℝ (h.eigenbasis i) (x : E)) ^ 2‖ ≤
          4 * (i.1⁻¹ * inner ℝ (h.eigenbasis i) (x : E)) ^ 2 := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact h.heatCurve_slope_error_bound x hs ht.1
  have hd := tendsto_tsum_of_dominated_convergence
    ((h.hasSum_inverse_norm x).summable.mul_left 4) hp hb
  have hd₀ : Tendsto (fun t : ℝ =>
      ∑' i : CompactSpectralIndex T,
        ((slope (fun r : ℝ => Real.exp (-r / i.1)) s t + i.1⁻¹ * Real.exp (-s / i.1)) *
          inner ℝ (h.eigenbasis i) (x : E)) ^ 2) L (𝓝 (0 : ℝ)) := by
    simpa only [tsum_zero] using hd
  have hn : Tendsto (fun t : ℝ =>
      ‖slope (h.heatCurve (x : E)) s t + h.heatCurve (inverseOperator T h.injective x) s‖ ^ 2)
      L (𝓝 (0 : ℝ)) := by
    apply hd₀.congr'
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact (h.heatCurve_slope_error_sq x hs ht.1).symm
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hn
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

theorem CompactPositiveInverse.heatCurve_right_derivative_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain) :
    HasDerivWithinAt (h.heatCurve (x : E)) (-inverseOperator T h.injective x) (Ici 0) 0 := by
  simpa only [h.heatCurve_zero] using h.heatCurve_hasDerivWithinAt x (show (0 : ℝ) ≤ 0 by rfl)

theorem CompactPositiveInverse.heatCurve_hasDerivAt {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (h.heatCurve (x : E))
      (-inverseOperator T h.injective
        ⟨h.heatCurve (x : E) s, h.heatCurve_mem_inverse_domain x s⟩) s := by
  have hd := (h.heatCurve_hasDerivWithinAt x hs.le).hasDerivAt (Ici_mem_nhds hs)
  simpa only [CompactPositiveInverse.heatCurve, h.inverse_heatSemigroup] using hd

end TimeTraps.Analysis
