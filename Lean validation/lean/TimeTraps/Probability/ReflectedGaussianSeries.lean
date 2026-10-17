module

public import TimeTraps.Analysis.GaussianLatticeBounds
public import TimeTraps.Probability.ReflectedGaussianKernel
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-! The genuine two-preimage Gaussian series is absolutely summable at
every spatial point. Its sum represents the already defined ENNReal
kernel, which is therefore finite pointwise. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal ENNReal

def reflectedGaussianTerm (L x : ℝ) (v : ℝ≥0) (k : ℤ) (y : ℝ) : ℝ :=
  gaussianPDFReal x v (y + k * (2 * L)) + gaussianPDFReal x v (k * (2 * L) - y)

theorem reflectedGaussianTerm_nonneg (L x : ℝ) (v : ℝ≥0) (k : ℤ) (y : ℝ) :
    0 ≤ reflectedGaussianTerm L x v k y :=
  add_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

theorem reflectedGaussianTerm_bound (L x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    ‖reflectedGaussianTerm L x v k y‖ ≤ 2 * gaussianLatticeMajorant L x v R k := by
  rw [Real.norm_eq_abs, abs_of_nonneg (reflectedGaussianTerm_nonneg L x v k y)]
  have hp := gaussianPDFReal_lattice_bound L x hv hy k
  have hm := gaussianPDFReal_lattice_bound L x hv (y := -y) (R := R)
    (by simpa only [abs_neg] using hy) k
  rw [show -y + (k : ℝ) * (2 * L) = k * (2 * L) - y by ring] at hm
  unfold reflectedGaussianTerm
  linarith

theorem reflectedGaussianTerm_summable {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) : Summable (fun k : ℤ => reflectedGaussianTerm L x v k y) :=
  ((gaussianLatticeMajorant_summable hL x hv |y|).mul_left 2).of_norm_bounded
    (fun k => reflectedGaussianTerm_bound L x hv le_rfl k)

theorem reflectedGaussianKernel_eq_ofReal_tsum {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) :
    reflectedGaussianKernel L x v y = ENNReal.ofReal (∑' k : ℤ, reflectedGaussianTerm L x v k y) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => reflectedGaussianTerm_nonneg L x v k y)
    (reflectedGaussianTerm_summable hL x hv y)]
  unfold reflectedGaussianKernel reflectedFoldDensity
  apply tsum_congr
  intro k
  exact (ENNReal.ofReal_add (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)).symm

theorem reflectedGaussianKernel_ne_top {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) : reflectedGaussianKernel L x v y ≠ ∞ := by
  rw [reflectedGaussianKernel_eq_ofReal_tsum hL x hv y]
  exact ENNReal.ofReal_ne_top

end TimeTraps.Probability

end
