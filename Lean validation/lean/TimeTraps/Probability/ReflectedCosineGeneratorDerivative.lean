module

public import TimeTraps.Probability.ReflectedCosineGeneratorData
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-! Sufficiency of the exact cosine coefficient condition for a strong
right derivative of the actual L2 evolution. Parseval and dominated
convergence control the full difference quotient, including the zero mode. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedCosineScalar_slope_error_sq_bound (L : ℝ) (n : ℕ) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖((slope (fun r : ℝ => Real.exp (-r * reflectedCosineRate L n)) 0 t +
      reflectedCosineRate L n) * c) ^ 2‖ ≤ 4 * (reflectedCosineRate L n * c) ^ 2 := by
  let a := slope (fun r : ℝ => Real.exp (-r * reflectedCosineRate L n)) 0 t + reflectedCosineRate L n
  change ‖(a * c) ^ 2‖ ≤ 4 * (reflectedCosineRate L n * c) ^ 2
  have ha : |a| ≤ 2 * reflectedCosineRate L n := reflectedCosineScalar_slope_error_bound L n ht
  have hm : |a * c| ≤ 2 * |reflectedCosineRate L n * c| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (reflectedCosineRate_nonneg L n)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ha (abs_nonneg c)
  have hs := (sq_le_sq₀ (abs_nonneg (a * c))
    (show 0 ≤ 2 * |reflectedCosineRate L n * c| by positivity)).mpr hm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (a * c), sq_abs (reflectedCosineRate L n * c)]

theorem reflectedGaussianL2Curve_slope_error_coefficient (L : ℝ) (hL : 0 < L)
    {f g : ReflectedUniformL2 L hL}
    (hg : ∀ n, inner ℝ (reflectedCosineHilbertBasis L hL n) g =
      -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    inner ℝ (reflectedCosineHilbertBasis L hL n) (slope (reflectedGaussianL2Curve L hL f) 0 t - g) =
      (slope (fun r : ℝ => Real.exp (-r * reflectedCosineRate L n)) 0 t + reflectedCosineRate L n) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  rw [slope_def_module, inner_sub_right, inner_smul_right, inner_sub_right,
    reflectedGaussianL2Curve_coefficient L hL f ht,
    reflectedGaussianL2Curve_coefficient L hL f le_rfl, hg, slope_def_field]
  ring

theorem reflectedGaussianL2Curve_slope_error_sq (L : ℝ) (hL : 0 < L)
    {f g : ReflectedUniformL2 L hL}
    (hg : ∀ n, inner ℝ (reflectedCosineHilbertBasis L hL n) g =
      -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖slope (reflectedGaussianL2Curve L hL f) 0 t - g‖ ^ 2 =
      ∑' n : ℕ, ((slope (fun r : ℝ => Real.exp (-r * reflectedCosineRate L n)) 0 t +
        reflectedCosineRate L n) * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2 := by
  rw [← (reflectedCosineBasis_hasSum_parseval L hL
    (slope (reflectedGaussianL2Curve L hL f) 0 t - g)).tsum_eq]
  apply tsum_congr
  intro n
  rw [reflectedGaussianL2Curve_slope_error_coefficient L hL hg ht]

theorem reflectedGaussianL2Curve_hasDerivWithinAt_of_coefficients (L : ℝ) (hL : 0 < L)
    {f g : ReflectedUniformL2 L hL}
    (hg : ∀ n, inner ℝ (reflectedCosineHilbertBasis L hL n) g =
      -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) :
    HasDerivWithinAt (reflectedGaussianL2Curve L hL f) g (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  let F : Filter ℝ := 𝓝[Ici 0 \ {(0 : ℝ)}] 0
  have hp : ∀ n : ℕ, Tendsto (fun t : ℝ =>
      ((slope (fun r : ℝ => Real.exp (-r * reflectedCosineRate L n)) 0 t + reflectedCosineRate L n) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) F (𝓝 (0 : ℝ)) := by
    intro n
    have hs := (reflectedCosineScalar_hasDerivAt L n).tendsto_slope.mono_left
      (nhdsWithin_mono (0 : ℝ) (show Ici 0 \ {(0 : ℝ)} ⊆ {(0 : ℝ)}ᶜ from fun _ ht => ht.2))
    simpa only [neg_add_cancel, zero_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      using ((hs.add_const (reflectedCosineRate L n)).mul_const
        (inner ℝ (reflectedCosineHilbertBasis L hL n) f)).pow 2
  have he : (fun n : ℕ => (reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) =
      (fun n : ℕ => (inner ℝ (reflectedCosineHilbertBasis L hL n) g) ^ 2) := by
    funext n
    rw [hg]
    ring
  have hd : Summable (fun n : ℕ => 4 *
      (reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) := by
    apply Summable.mul_left
    rw [he]
    exact (reflectedCosineBasis_hasSum_parseval L hL g).summable
  have hb : ∀ᶠ t in F, ∀ n : ℕ,
      ‖((slope (fun r : ℝ => Real.exp (-r * reflectedCosineRate L n)) 0 t + reflectedCosineRate L n) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2‖ ≤
      4 * (reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2 := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact fun n => reflectedCosineScalar_slope_error_sq_bound L n _ ht.1
  have hlim := tendsto_tsum_of_dominated_convergence hd hp hb
  have hn : Tendsto (fun t : ℝ => ‖slope (reflectedGaussianL2Curve L hL f) 0 t - g‖ ^ 2)
      F (𝓝 (0 : ℝ)) := by
    simp only [tsum_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact (reflectedGaussianL2Curve_slope_error_sq L hL hg ht.1).symm
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hn
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

end TimeTraps.Probability
