module

public import TimeTraps.Probability.ReflectedGaussianSeries
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! A real-valued representation of the already proved finite Gaussian
kernel. Its actual lattice partial sums converge uniformly on every
compact spatial set. The density is continuous and strictly positive on
the whole real line, in particular at both reflecting endpoints. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedGaussianDensity (L x : ℝ) (v : ℝ≥0) (y : ℝ) : ℝ :=
  (reflectedGaussianKernel L x v y).toReal

theorem reflectedGaussianDensity_eq_tsum {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) :
    reflectedGaussianDensity L x v y = ∑' k : ℤ, reflectedGaussianTerm L x v k y := by
  unfold reflectedGaussianDensity
  rw [reflectedGaussianKernel_eq_ofReal_tsum hL x hv y,
    ENNReal.toReal_ofReal (tsum_nonneg (fun k => reflectedGaussianTerm_nonneg L x v k y))]

theorem reflectedGaussianDensity_uniformOn_compact {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun J : Finset ℤ => fun y => ∑ k ∈ J, reflectedGaussianTerm L x v k y)
      (reflectedGaussianDensity L x v) atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hu := tendstoUniformlyOn_tsum ((gaussianLatticeMajorant_summable hL x hv R).mul_left 2)
    (fun k y hy => reflectedGaussianTerm_bound L x hv
      (show |y| ≤ R by simpa only [Real.norm_eq_abs] using hR y hy) k)
  exact hu.congr_right (fun y _ => (reflectedGaussianDensity_eq_tsum hL x hv y).symm)

theorem reflectedGaussianDensity_continuous {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : Continuous (reflectedGaussianDensity L x v) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  let R : ℝ := |y| + 1
  have hc : ContinuousOn (reflectedGaussianDensity L x v) (Icc (-R) R) := by
    apply (reflectedGaussianDensity_uniformOn_compact hL x hv isCompact_Icc).continuousOn
    apply Filter.Frequently.of_forall
    intro J
    apply continuousOn_finsetSum
    intro k _
    unfold reflectedGaussianTerm gaussianPDFReal
    fun_prop
  apply hc.continuousAt
  apply Icc_mem_nhds
  · dsimp [R]
    linarith [neg_abs_le y]
  · dsimp [R]
    linarith [le_abs_self y]

theorem reflectedGaussianDensity_pos {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) : 0 < reflectedGaussianDensity L x v y := by
  rw [reflectedGaussianDensity_eq_tsum hL x hv y]
  apply (reflectedGaussianTerm_summable hL x hv y).tsum_pos
    (fun k => reflectedGaussianTerm_nonneg L x v k y) (0 : ℤ)
  exact add_pos_of_pos_of_nonneg (gaussianPDFReal_pos _ _ _ (ne_of_gt hv))
    (gaussianPDFReal_nonneg _ _ _)

theorem reflectedGaussianKernel_continuous {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : Continuous (reflectedGaussianKernel L x v) := by
  have he : reflectedGaussianKernel L x v =
      fun y => ENNReal.ofReal (reflectedGaussianDensity L x v y) := by
    funext y
    rw [reflectedGaussianDensity_eq_tsum hL x hv y]
    exact reflectedGaussianKernel_eq_ofReal_tsum hL x hv y
  rw [he]
  exact ENNReal.continuous_ofReal.comp (reflectedGaussianDensity_continuous hL x hv)

end TimeTraps.Probability

end
