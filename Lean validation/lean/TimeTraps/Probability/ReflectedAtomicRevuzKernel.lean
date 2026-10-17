module

public import TimeTraps.Probability.ReflectedAtomicRevuzContact
public import TimeTraps.Probability.ReflectedGaussianSymmetry
public import TimeTraps.Probability.ReflectedFellerIntegral

@[expose] public section

/-! Spatial integration of the actual reflected Gaussian density against
a continuous interval test. Symmetry identifies it with the actual
Feller operator. Kernel mass one supplies the norm bound required for
time-space Fubini, without a bound on the density near time zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedAtomicRevuzKernel_integrable (L : ℝ) (hL : 0 < L)
    (a : Icc (0 : ℝ) L) (h : C(Icc (0 : ℝ) L, ℝ)) {v : ℝ≥0} (hv : 0 < v) :
    IntegrableOn (fun x => reflectedFellerExtension L hL h x * reflectedGaussianDensity L x v a.val)
      (Ioo (0 : ℝ) L) volume := by
  have hg : Integrable (reflectedFellerExtension L hL h) (reflectedGaussianLaw L a.val v) :=
    (integrable_const ‖h‖).mono' (reflectedFellerExtension L hL h).continuous.aestronglyMeasurable
      (Eventually.of_forall (reflectedFellerExtension_bound L hL h))
  have hf : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) L), reflectedGaussianKernel L a.val v x < ∞ :=
    Eventually.of_forall (fun x => lt_top_iff_ne_top.mpr (reflectedGaussianKernel_ne_top hL a.val hv x))
  rw [reflectedGaussianLaw_density L hL a.val (ne_of_gt hv)] at hg
  have hi := (integrable_withDensity_iff_integrable_smul'
    (reflectedGaussianKernel_measurable L a.val v) hf).mp hg
  apply hi.congr
  filter_upwards [] with x
  change reflectedGaussianDensity L a.val v x * reflectedFellerExtension L hL h x = _
  rw [reflectedGaussianDensity_symmetric L a.val x v, mul_comm]

theorem reflectedAtomicRevuzKernel_integral (L : ℝ) (hL : 0 < L)
    (a : Icc (0 : ℝ) L) (h : C(Icc (0 : ℝ) L, ℝ)) {v : ℝ≥0} (hv : 0 < v) :
    (∫ x in Ioo (0 : ℝ) L,
      reflectedFellerExtension L hL h x * reflectedGaussianDensity L x v a.val) =
        reflectedFellerOperator L hL v h a := by
  rw [reflectedFellerOperator_kernel, reflectedGaussianLaw_density L hL a.val (ne_of_gt hv),
    integral_withDensity_eq_integral_toReal_smul (reflectedGaussianKernel_measurable L a.val v)
      (Eventually.of_forall (fun x => lt_top_iff_ne_top.mpr (reflectedGaussianKernel_ne_top hL a.val hv x)))]
  apply integral_congr_ae
  filter_upwards [] with x
  change reflectedFellerExtension L hL h x * reflectedGaussianDensity L x v a.val =
    reflectedGaussianDensity L a.val v x * reflectedFellerExtension L hL h x
  rw [reflectedGaussianDensity_symmetric L a.val x v, mul_comm]

theorem reflectedAtomicRevuzKernel_integral_norm_le (L : ℝ) (hL : 0 < L)
    (a : Icc (0 : ℝ) L) (h : C(Icc (0 : ℝ) L, ℝ)) {v : ℝ≥0} (hv : 0 < v) :
    (∫ x in Ioo (0 : ℝ) L,
      ‖reflectedFellerExtension L hL h x * reflectedGaussianDensity L x v a.val‖) ≤ ‖h‖ := by
  have he : (∫ x in Ioo (0 : ℝ) L,
      ‖reflectedFellerExtension L hL h x * reflectedGaussianDensity L x v a.val‖) =
      ∫ x, ‖reflectedFellerExtension L hL h x‖ ∂reflectedGaussianLaw L a.val v := by
    rw [reflectedGaussianLaw_density L hL a.val (ne_of_gt hv),
      integral_withDensity_eq_integral_toReal_smul (reflectedGaussianKernel_measurable L a.val v)
        (Eventually.of_forall (fun x => lt_top_iff_ne_top.mpr (reflectedGaussianKernel_ne_top hL a.val hv x)))]
    apply integral_congr_ae
    filter_upwards [] with x
    change ‖reflectedFellerExtension L hL h x * reflectedGaussianDensity L x v a.val‖ =
      reflectedGaussianDensity L a.val v x * ‖reflectedFellerExtension L hL h x‖
    have hk : 0 ≤ reflectedGaussianDensity L x v a.val := ENNReal.toReal_nonneg
    rw [norm_mul, Real.norm_eq_abs (reflectedGaussianDensity L x v a.val),
      abs_of_nonneg hk, reflectedGaussianDensity_symmetric L a.val x v, mul_comm]
  rw [he]
  have hg : Integrable (reflectedFellerExtension L hL h) (reflectedGaussianLaw L a.val v) :=
    (integrable_const ‖h‖).mono' (reflectedFellerExtension L hL h).continuous.aestronglyMeasurable
      (Eventually.of_forall (reflectedFellerExtension_bound L hL h))
  calc
    _ ≤ ∫ _ : ℝ, ‖h‖ ∂reflectedGaussianLaw L a.val v :=
      integral_mono hg.norm (integrable_const _) (reflectedFellerExtension_bound L hL h)
    _ = _ := by simp

theorem reflectedAtomicRevuzKernel_jointlyMeasurable (L : ℝ) (hL : 0 < L) (D a : ℝ)
    (h : C(Icc (0 : ℝ) L, ℝ)) :
    Measurable (fun p : ℝ × ℝ => reflectedFellerExtension L hL h p.2 *
      reflectedGaussianDensity L p.2 (2 * D * p.1).toNNReal a) := by
  have hk : Measurable (fun p : ℝ × ℝ => reflectedGaussianKernel L a (2 * D * p.1).toNNReal p.2) := by
    unfold reflectedGaussianKernel reflectedFoldDensity gaussianPDF gaussianPDFReal
    apply Measurable.tsum
    intro k
    fun_prop
  have he : (fun p : ℝ × ℝ => reflectedFellerExtension L hL h p.2 *
      reflectedGaussianDensity L p.2 (2 * D * p.1).toNNReal a) =
      (fun p : ℝ × ℝ => reflectedFellerExtension L hL h p.2 *
        (reflectedGaussianKernel L a (2 * D * p.1).toNNReal p.2).toReal) := by
    funext p
    rw [reflectedGaussianDensity_symmetric L p.2 a]
    rfl
  rw [he]
  exact ((reflectedFellerExtension L hL h).continuous.measurable.comp measurable_snd).mul hk.ennreal_toReal

end TimeTraps.Probability
