module

public import TimeTraps.Probability.ReflectedGaussianL2Operator
public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-! Identification of the full L2 operator with actual kernel averaging
on bounded Borel inputs, including square Jensen's inequality. The
averaged function is independently proved square-integrable before its
Lp equivalence class is compared with the joint-law construction. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal ProbabilityTheory

theorem reflectedGaussianLaw_integral_sq_le (L x : ℝ) (v : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) :
    (∫ y, g y ∂reflectedGaussianLaw L x v) ^ 2 ≤
      ∫ y, (g y) ^ 2 ∂reflectedGaussianLaw L x v := by
  have hg2 : MemLp g 2 (reflectedGaussianLaw L x v) :=
    MemLp.of_bound hg.aestronglyMeasurable M (Eventually.of_forall hb)
  have h := memLp_integral_mul_sq_le hg2
    (memLp_const (μ := reflectedGaussianLaw L x v) (p := 2) (1 : ℝ))
  simpa only [mul_one, one_pow, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, smul_eq_mul] using h

theorem reflectedGaussianAverage_memLp (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) :
    MemLp (fun x => ∫ y, g y ∂reflectedGaussianLaw L x v) 2 (reflectedUniformLaw L hL) := by
  apply MemLp.of_bound (reflectedGaussianLaw_integral_measurable L v hg).aestronglyMeasurable M
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using reflectedGaussianLaw_integral_bound L x v hb

theorem reflectedGaussianL2Operator_toLp_average (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M)
    (hg2 : MemLp g 2 (reflectedUniformLaw L hL)) :
    reflectedGaussianL2Operator L hL v (hg2.toLp g) =
      (reflectedGaussianAverage_memLp L hL v hg hb).toLp
        (fun x => ∫ y, g y ∂reflectedGaussianLaw L x v) := by
  apply ext_inner_left ℝ
  intro f
  rw [reflectedGaussianL2Operator_pairing, L2.inner_def]
  have hga : ∀ᵐ p ∂reflectedGaussianJoint L hL v, (hg2.toLp g) p.2 = g p.2 :=
    (reflectedGaussianJoint_snd_preserving L hL v).quasiMeasurePreserving.ae hg2.coeFn_toLp
  have hi : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) (reflectedGaussianJoint L hL v) := by
    apply (reflectedGaussianJoint_integrable_mul L hL v f (hg2.toLp g)).congr
    filter_upwards [hga] with p hp
    rw [hp]
  calc
    _ = ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂reflectedGaussianJoint L hL v := by
      apply integral_congr_ae
      filter_upwards [hga] with p hp
      rw [hp]
    _ = ∫ x, f x * (∫ y, g y ∂reflectedGaussianLaw L x v) ∂reflectedUniformLaw L hL := by
      change (∫ p : ℝ × ℝ, f p.1 * g p.2
        ∂((reflectedUniformLaw L hL) ⊗ₘ (reflectedGaussianTransition L v))) = _
      rw [Measure.integral_compProd hi]
      simp only [integral_const_mul, reflectedGaussianTransition_apply]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(reflectedGaussianAverage_memLp L hL v hg hb).coeFn_toLp] with x hx
      simp only [Real.inner_apply, hx]

theorem reflectedGaussianL2Operator_bounded_coe (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M)
    (hg2 : MemLp g 2 (reflectedUniformLaw L hL)) :
    (reflectedGaussianL2Operator L hL v (hg2.toLp g) : ℝ → ℝ) =ᵐ[reflectedUniformLaw L hL]
      fun x => ∫ y, g y ∂reflectedGaussianLaw L x v := by
  rw [reflectedGaussianL2Operator_toLp_average L hL v hg hb hg2]
  exact (reflectedGaussianAverage_memLp L hL v hg hb).coeFn_toLp

end TimeTraps.Probability
