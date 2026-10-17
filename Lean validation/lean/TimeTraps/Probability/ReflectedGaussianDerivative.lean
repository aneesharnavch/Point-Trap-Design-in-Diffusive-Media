module

public import TimeTraps.Analysis.GaussianLatticeDerivative
public import TimeTraps.Probability.ReflectedGaussianRegularity

@[expose] public section

/-! Differentiating the actual reflected Gaussian series. The derivative
series has a summable uniform majorant on each compact spatial set. This
proves the derivative formula and continuous first differentiability for
every positive length and variance. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedGaussianTermDerivative (L x : ℝ) (v : ℝ≥0) (k : ℤ) (y : ℝ) : ℝ :=
  gaussianPDFDerivative x v (y + k * (2 * L)) - gaussianPDFDerivative x v (k * (2 * L) - y)

def reflectedGaussianDensityDerivative (L x : ℝ) (v : ℝ≥0) (y : ℝ) : ℝ :=
  ∑' k : ℤ, reflectedGaussianTermDerivative L x v k y

theorem reflectedGaussianTerm_hasDerivAt (L x : ℝ) {v : ℝ≥0} (hv : 0 < v) (k : ℤ) (y : ℝ) :
    HasDerivAt (reflectedGaussianTerm L x v k) (reflectedGaussianTermDerivative L x v k y) y := by
  have hp := (gaussianPDFReal_hasDerivAt x hv (y + k * (2 * L))).comp y
    ((hasDerivAt_id y).add_const (k * (2 * L)))
  have hm := (gaussianPDFReal_hasDerivAt x hv (k * (2 * L) - y)).comp y
    ((hasDerivAt_id y).const_sub (k * (2 * L)))
  apply (hp.add hm).congr_deriv
  simp only [reflectedGaussianTermDerivative, mul_one, mul_neg_one, sub_eq_add_neg]

theorem reflectedGaussianTermDerivative_bound {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    ‖reflectedGaussianTermDerivative L x v k y‖ ≤ 2 * gaussianLatticeDerivativeMajorant L x v R k := by
  have hp := gaussianPDFDerivative_lattice_bound hL x hv hy k
  have hm := gaussianPDFDerivative_lattice_bound hL x hv (y := -y) (R := R)
    (by simpa only [abs_neg] using hy) k
  rw [show -y + (k : ℝ) * (2 * L) = k * (2 * L) - y by ring] at hm
  exact (norm_sub_le _ _).trans (by linarith)

theorem reflectedGaussianTermDerivative_summable {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) :
    Summable (fun k : ℤ => reflectedGaussianTermDerivative L x v k y) :=
  ((gaussianLatticeDerivativeMajorant_summable hL x hv |y|).mul_left 2).of_norm_bounded
    (fun k => reflectedGaussianTermDerivative_bound hL x hv le_rfl k)

theorem reflectedGaussianDensity_hasDerivAt {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) :
    HasDerivAt (reflectedGaussianDensity L x v) (reflectedGaussianDensityDerivative L x v y) y := by
  let R : ℝ := |y| + 1
  have hy : y ∈ Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le y, le_abs_self y]
  have h := hasDerivAt_tsum_of_isPreconnected
    ((gaussianLatticeDerivativeMajorant_summable hL x hv R).mul_left 2)
    isOpen_Ioo isPreconnected_Ioo
    (fun k z _ => reflectedGaussianTerm_hasDerivAt L x hv k z)
    (fun k z hz => reflectedGaussianTermDerivative_bound hL x hv
      (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) k)
    hy (reflectedGaussianTerm_summable hL x hv y) hy
  have he : reflectedGaussianDensity L x v = fun z => ∑' k : ℤ, reflectedGaussianTerm L x v k z :=
    funext (reflectedGaussianDensity_eq_tsum hL x hv)
  rw [he]
  exact h

theorem reflectedGaussianDensityDerivative_uniformOn_compact {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun J : Finset ℤ => fun y => ∑ k ∈ J, reflectedGaussianTermDerivative L x v k y)
      (reflectedGaussianDensityDerivative L x v) atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact tendstoUniformlyOn_tsum ((gaussianLatticeDerivativeMajorant_summable hL x hv R).mul_left 2)
    (fun k y hy => reflectedGaussianTermDerivative_bound hL x hv
      (show |y| ≤ R by simpa only [Real.norm_eq_abs] using hR y hy) k)

theorem reflectedGaussianDensityDerivative_continuous {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : Continuous (reflectedGaussianDensityDerivative L x v) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  let R : ℝ := |y| + 1
  have hc : ContinuousOn (reflectedGaussianDensityDerivative L x v) (Icc (-R) R) := by
    apply (reflectedGaussianDensityDerivative_uniformOn_compact hL x hv isCompact_Icc).continuousOn
    apply Filter.Frequently.of_forall
    intro J
    apply continuousOn_finsetSum
    intro k _
    unfold reflectedGaussianTermDerivative gaussianPDFDerivative gaussianPDFReal
    fun_prop
  apply hc.continuousAt
  apply Icc_mem_nhds
  · dsimp [R]
    linarith [neg_abs_le y]
  · dsimp [R]
    linarith [le_abs_self y]

theorem reflectedGaussianDensity_contDiff_one {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : ContDiff ℝ 1 (reflectedGaussianDensity L x v) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun y => (reflectedGaussianDensity_hasDerivAt hL x hv y).differentiableAt, ?_⟩
  have he : deriv (reflectedGaussianDensity L x v) = reflectedGaussianDensityDerivative L x v :=
    funext (fun y => (reflectedGaussianDensity_hasDerivAt hL x hv y).deriv)
  rw [he]
  exact reflectedGaussianDensityDerivative_continuous hL x hv

end TimeTraps.Probability

end
