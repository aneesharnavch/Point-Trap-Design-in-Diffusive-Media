module

public import TimeTraps.Analysis.GaussianLatticeSecondDerivative
public import TimeTraps.Probability.ReflectedGaussianDerivative

@[expose] public section

/-! The actual reflected Gaussian density is twice continuously
differentiable in space. The second derivative series converges uniformly
on every compact spatial set, by the proved quadratic geometric bound.
The variance remains fixed and positive throughout these statements. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology ContDiff

def reflectedGaussianTermSecondDerivative (L x : ℝ) (v : ℝ≥0) (k : ℤ) (y : ℝ) : ℝ :=
  gaussianPDFSecondDerivative x v (y + k * (2 * L)) +
    gaussianPDFSecondDerivative x v (k * (2 * L) - y)

def reflectedGaussianDensitySecondDerivative (L x : ℝ) (v : ℝ≥0) (y : ℝ) : ℝ :=
  ∑' k : ℤ, reflectedGaussianTermSecondDerivative L x v k y

theorem reflectedGaussianTermDerivative_hasDerivAt (L x : ℝ) {v : ℝ≥0}
    (hv : 0 < v) (k : ℤ) (y : ℝ) :
    HasDerivAt (reflectedGaussianTermDerivative L x v k)
      (reflectedGaussianTermSecondDerivative L x v k y) y := by
  have hp := (gaussianPDFDerivative_hasDerivAt x hv (y + k * (2 * L))).comp y
    ((hasDerivAt_id y).add_const (k * (2 * L)))
  have hm := (gaussianPDFDerivative_hasDerivAt x hv (k * (2 * L) - y)).comp y
    ((hasDerivAt_id y).const_sub (k * (2 * L)))
  apply (hp.sub hm).congr_deriv
  simp only [reflectedGaussianTermSecondDerivative, mul_one, mul_neg_one, sub_neg_eq_add]

theorem reflectedGaussianTermSecondDerivative_bound {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    ‖reflectedGaussianTermSecondDerivative L x v k y‖ ≤ 2 * gaussianLatticeSecondMajorant L x v R k := by
  have hp := gaussianPDFSecondDerivative_lattice_bound hL x hv hy k
  have hm := gaussianPDFSecondDerivative_lattice_bound hL x hv (y := -y) (R := R)
    (by simpa only [abs_neg] using hy) k
  rw [show -y + (k : ℝ) * (2 * L) = k * (2 * L) - y by ring] at hm
  exact (norm_add_le _ _).trans (by linarith)

theorem reflectedGaussianTermSecondDerivative_summable {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) :
    Summable (fun k : ℤ => reflectedGaussianTermSecondDerivative L x v k y) :=
  ((gaussianLatticeSecondMajorant_summable hL x hv |y|).mul_left 2).of_norm_bounded
    (fun k => reflectedGaussianTermSecondDerivative_bound hL x hv le_rfl k)

theorem reflectedGaussianDensityDerivative_hasDerivAt {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) :
    HasDerivAt (reflectedGaussianDensityDerivative L x v)
      (reflectedGaussianDensitySecondDerivative L x v y) y := by
  let R : ℝ := |y| + 1
  have hy : y ∈ Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le y, le_abs_self y]
  exact hasDerivAt_tsum_of_isPreconnected
    ((gaussianLatticeSecondMajorant_summable hL x hv R).mul_left 2)
    isOpen_Ioo isPreconnected_Ioo
    (fun k z _ => reflectedGaussianTermDerivative_hasDerivAt L x hv k z)
    (fun k z hz => reflectedGaussianTermSecondDerivative_bound hL x hv
      (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) k)
    hy (reflectedGaussianTermDerivative_summable hL x hv y) hy

theorem reflectedGaussianDensitySecondDerivative_uniformOn_compact {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun J : Finset ℤ => fun y => ∑ k ∈ J, reflectedGaussianTermSecondDerivative L x v k y)
      (reflectedGaussianDensitySecondDerivative L x v) atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact tendstoUniformlyOn_tsum ((gaussianLatticeSecondMajorant_summable hL x hv R).mul_left 2)
    (fun k y hy => reflectedGaussianTermSecondDerivative_bound hL x hv
      (show |y| ≤ R by simpa only [Real.norm_eq_abs] using hR y hy) k)

theorem reflectedGaussianDensitySecondDerivative_continuous {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : Continuous (reflectedGaussianDensitySecondDerivative L x v) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  let R : ℝ := |y| + 1
  have hc : ContinuousOn (reflectedGaussianDensitySecondDerivative L x v) (Icc (-R) R) := by
    apply (reflectedGaussianDensitySecondDerivative_uniformOn_compact hL x hv isCompact_Icc).continuousOn
    apply Filter.Frequently.of_forall
    intro J
    apply continuousOn_finsetSum
    intro k _
    unfold reflectedGaussianTermSecondDerivative gaussianPDFSecondDerivative gaussianPDFReal
    fun_prop
  apply hc.continuousAt
  apply Icc_mem_nhds
  · dsimp [R]
    linarith [neg_abs_le y]
  · dsimp [R]
    linarith [le_abs_self y]

theorem reflectedGaussianDensity_contDiff_two {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) : ContDiff ℝ 2 (reflectedGaussianDensity L x v) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun y => (reflectedGaussianDensity_hasDerivAt hL x hv y).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · have he : deriv (reflectedGaussianDensity L x v) = reflectedGaussianDensityDerivative L x v :=
      funext (fun y => (reflectedGaussianDensity_hasDerivAt hL x hv y).deriv)
    rw [he]
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun y => (reflectedGaussianDensityDerivative_hasDerivAt hL x hv y).differentiableAt, ?_⟩
    have he₂ : deriv (reflectedGaussianDensityDerivative L x v) =
        reflectedGaussianDensitySecondDerivative L x v :=
      funext (fun y => (reflectedGaussianDensityDerivative_hasDerivAt hL x hv y).deriv)
    rw [he₂]
    exact reflectedGaussianDensitySecondDerivative_continuous hL x hv

theorem reflectedGaussianDensity_second_deriv {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (y : ℝ) :
    deriv (deriv (reflectedGaussianDensity L x v)) y = reflectedGaussianDensitySecondDerivative L x v y := by
  have he : deriv (reflectedGaussianDensity L x v) = reflectedGaussianDensityDerivative L x v :=
    funext (fun z => (reflectedGaussianDensity_hasDerivAt hL x hv z).deriv)
  rw [he]
  exact (reflectedGaussianDensityDerivative_hasDerivAt hL x hv y).deriv

end TimeTraps.Probability

end
