module

public import TimeTraps.Analysis.GaussianVarianceDerivative
public import TimeTraps.Analysis.GaussianVarianceLatticeBounds
public import TimeTraps.Probability.ReflectedGaussianSecondDerivative

@[expose] public section

/-! The actual image density satisfies the variance heat equation at
every positive variance, and the physical time equation after v = 2Dt.
Exchange of variance differentiation and summation uses the proved bound
uniform on a positive variance neighborhood. No generator-domain or
stochastic differential assertion is inferred here. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedGaussianTerm_variance_hasDerivAt (L x y : ℝ) (k : ℤ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => reflectedGaussianTerm L x w.toNNReal k y)
      ((1 / 2 : ℝ) * reflectedGaussianTermSecondDerivative L x v.toNNReal k y) v := by
  have hp := gaussianPDFReal_variance_hasDerivAt x (y + k * (2 * L)) hv
  have hm := gaussianPDFReal_variance_hasDerivAt x (k * (2 * L) - y) hv
  apply (hp.add hm).congr_deriv
  unfold reflectedGaussianTermSecondDerivative
  ring

theorem reflectedGaussianTerm_variance_bound {L : ℝ} (hL : 0 < L) (x : ℝ)
    {a b v : ℝ≥0} (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b)
    {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    ‖(1 / 2 : ℝ) * reflectedGaussianTermSecondDerivative L x v k y‖ ≤
      gaussianVarianceSecondMajorant L x a b R k := by
  have hp := gaussianPDFSecondDerivative_variance_bound hL x ha hav hvb hy k
  have hm := gaussianPDFSecondDerivative_variance_bound hL x ha hav hvb (y := -y) (R := R)
    (by simpa only [abs_neg] using hy) k
  rw [show -y + (k : ℝ) * (2 * L) = k * (2 * L) - y by ring] at hm
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hn := norm_add_le (gaussianPDFSecondDerivative x v (y + k * (2 * L)))
    (gaussianPDFSecondDerivative x v (k * (2 * L) - y))
  unfold reflectedGaussianTermSecondDerivative
  linarith

theorem reflectedGaussianDensity_variance_hasDerivAt {L : ℝ} (hL : 0 < L) (x y : ℝ)
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => reflectedGaussianDensity L x w.toNNReal y)
      ((1 / 2 : ℝ) * reflectedGaussianDensitySecondDerivative L x v.toNNReal y) v := by
  let a : ℝ≥0 := NNReal.mk (v / 2) (by positivity)
  let b : ℝ≥0 := NNReal.mk (2 * v) (by positivity)
  have ha : 0 < a := by change (0 : ℝ) < v / 2; positivity
  have hb : 0 < b := by change (0 : ℝ) < 2 * v; positivity
  have hi : v ∈ Ioo (v / 2) (2 * v) := by constructor <;> linarith
  have hwpos : ∀ w ∈ Ioo (v / 2) (2 * v), 0 < w := by
    intro w hw
    linarith [hw.1]
  have haw : ∀ w ∈ Ioo (v / 2) (2 * v), a ≤ w.toNNReal := by
    intro w hw
    change v / 2 ≤ (w.toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (hwpos w hw).le]
    exact hw.1.le
  have hwb : ∀ w ∈ Ioo (v / 2) (2 * v), w.toNNReal ≤ b := by
    intro w hw
    change (w.toNNReal : ℝ) ≤ 2 * v
    rw [Real.coe_toNNReal _ (hwpos w hw).le]
    exact hw.2.le
  have h := hasDerivAt_tsum_of_isPreconnected
    (gaussianVarianceSecondMajorant_summable hL x a hb |y|)
    isOpen_Ioo isPreconnected_Ioo
    (fun k w hw => reflectedGaussianTerm_variance_hasDerivAt L x y k (hwpos w hw))
    (fun k w hw => reflectedGaussianTerm_variance_bound hL x ha (haw w hw) (hwb w hw) le_rfl k)
    hi (reflectedGaussianTerm_summable hL x (Real.toNNReal_pos.mpr hv) y) hi
  have hsum : (∑' k : ℤ, (1 / 2 : ℝ) * reflectedGaussianTermSecondDerivative L x v.toNNReal k y) =
      (1 / 2 : ℝ) * reflectedGaussianDensitySecondDerivative L x v.toNNReal y := by
    rw [tsum_mul_left]
    rfl
  apply (h.congr_deriv hsum).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hv] with w hw
  exact reflectedGaussianDensity_eq_tsum hL x (Real.toNNReal_pos.mpr hw) y

theorem reflectedGaussianDensity_variance_heatEquation {L : ℝ} (hL : 0 < L) (x y : ℝ)
    {v : ℝ} (hv : 0 < v) :
    deriv (fun w : ℝ => reflectedGaussianDensity L x w.toNNReal y) v =
      (1 / 2 : ℝ) * deriv (deriv (reflectedGaussianDensity L x v.toNNReal)) y := by
  rw [(reflectedGaussianDensity_variance_hasDerivAt hL x y hv).deriv,
    reflectedGaussianDensity_second_deriv hL x (Real.toNNReal_pos.mpr hv) y]

theorem reflectedGaussianDensity_time_hasDerivAt {L : ℝ} (hL : 0 < L) (x y : ℝ)
    {D t : ℝ} (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => reflectedGaussianDensity L x (2 * D * s).toNNReal y)
      (D * deriv (deriv (reflectedGaussianDensity L x (2 * D * t).toNNReal)) y) t := by
  have hv : 0 < 2 * D * t := mul_pos (mul_pos (by norm_num) hD) ht
  have h := (reflectedGaussianDensity_variance_hasDerivAt hL x y hv).comp t
    ((hasDerivAt_id t).const_mul (2 * D))
  apply h.congr_deriv
  rw [reflectedGaussianDensity_second_deriv hL x (Real.toNNReal_pos.mpr hv) y]
  ring

end TimeTraps.Probability
