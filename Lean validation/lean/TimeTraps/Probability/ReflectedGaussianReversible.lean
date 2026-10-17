module

public import TimeTraps.Probability.ReflectedGaussianSymmetry
public import TimeTraps.Probability.ReflectedGaussianTransition
public import Mathlib.Probability.Kernel.Invariance

@[expose] public section

/-! Normalized Lebesgue measure on the closed reflecting interval is a
reversible stationary probability law for the actual Gaussian transition
kernel. Positive variance uses its proved image density and Tonelli;
zero variance uses the identity Dirac law on the interval. The endpoints
have zero uniform mass, so the open-interval density gives the same law. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

def reflectedUniformLaw (L : ℝ) (_hL : 0 < L) : Measure ℝ :=
  (ENNReal.ofReal L)⁻¹ • volume.restrict (Icc 0 L)

theorem reflectedUniformLaw_eq_open (L : ℝ) (hL : 0 < L) :
    reflectedUniformLaw L hL = (ENNReal.ofReal L)⁻¹ • volume.restrict (Ioo 0 L) := by
  rw [reflectedUniformLaw, restrict_Ioo_eq_restrict_Icc]

instance reflectedUniformLaw_isProbabilityMeasure (L : ℝ) (hL : 0 < L) :
    IsProbabilityMeasure (reflectedUniformLaw L hL) where
  measure_univ := by
    simp only [reflectedUniformLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, smul_eq_mul, Real.volume_Icc, sub_zero]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top

theorem reflectedUniformLaw_ae_mem (L : ℝ) (hL : 0 < L) :
    ∀ᵐ x ∂reflectedUniformLaw L hL, x ∈ Icc 0 L :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem reflectedGaussianTransition_reversible_volume (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    Kernel.IsReversible (reflectedGaussianTransition L v) (volume.restrict (Ioo 0 L)) := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 L)
  by_cases hv : v = 0
  · subst v
    have he {A B : Set ℝ} (hB : MeasurableSet B) :
        (∫⁻ x in A, reflectedGaussianTransition L 0 x B ∂μ) = μ (B ∩ A) := by
      calc
        _ = ∫⁻ x in A, B.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioo)] with x hx
          rw [reflectedGaussianTransition_zero_apply L hL (Ioo_subset_Icc_self hx),
            Measure.dirac_apply' x hB]
          rfl
        _ = _ := by
          change (∫⁻ x, B.indicator (1 : ℝ → ℝ≥0∞) x ∂μ.restrict A) = _
          rw [lintegral_indicator_one hB, Measure.restrict_apply hB]
    intro A B hA hB
    change (∫⁻ x in A, reflectedGaussianTransition L 0 x B ∂μ) =
      ∫⁻ x in B, reflectedGaussianTransition L 0 x A ∂μ
    rw [he hB, he hA, inter_comm]
  · intro A B hA hB
    change (∫⁻ x in A, reflectedGaussianLaw L x v B ∂μ) =
      ∫⁻ x in B, reflectedGaussianLaw L x v A ∂μ
    calc
      _ = ∫⁻ x in A, ∫⁻ y in B, reflectedGaussianKernel L x v y ∂μ ∂μ := by
        simp_rw [reflectedGaussianLaw_density L hL _ hv, withDensity_apply _ hB]
        rfl
      _ = ∫⁻ y in B, ∫⁻ x in A, reflectedGaussianKernel L x v y ∂μ ∂μ :=
        lintegral_lintegral_swap (reflectedGaussianKernel_jointlyMeasurable L v).aemeasurable
      _ = _ := by
        simp_rw [reflectedGaussianKernel_symmetric L, reflectedGaussianLaw_density L hL _ hv,
          withDensity_apply _ hA]
        rfl

theorem reflectedGaussianTransition_reversible (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    Kernel.IsReversible (reflectedGaussianTransition L v) (reflectedUniformLaw L hL) := by
  intro A B hA hB
  rw [reflectedUniformLaw_eq_open]
  simp only [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  exact congrArg (fun z : ℝ≥0∞ => (ENNReal.ofReal L)⁻¹ * z)
    (reflectedGaussianTransition_reversible_volume L hL v hA hB)

theorem reflectedGaussianTransition_uniform_invariant (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    Kernel.Invariant (reflectedGaussianTransition L v) (reflectedUniformLaw L hL) :=
  (reflectedGaussianTransition_reversible L hL v).invariant

end TimeTraps.Probability

end
