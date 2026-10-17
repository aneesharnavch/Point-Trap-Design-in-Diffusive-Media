module

public import TimeTraps.Probability.ReflectedGaussianL2Feller
public import TimeTraps.Analysis.IntervalSobolevCompactL2

@[expose] public section

/-! Same-function identification of the actual normalized-uniform L2 space
with Lebesgue L2 on the open interval. Only the measure normalization
changes: squared norms and inner products acquire the factor L. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped ENNReal

theorem reflectedVolume_eq_smul_uniform (L : ℝ) (hL : 0 < L) :
    volume.restrict (Ioo 0 L) = ENNReal.ofReal L • reflectedUniformLaw L hL := by
  rw [reflectedUniformLaw_eq_open, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top, one_smul]

theorem reflectedUniformLaw_ae_iff (L : ℝ) (hL : 0 < L) (p : ℝ → Prop) :
    (∀ᵐ x ∂reflectedUniformLaw L hL, p x) ↔ ∀ᵐ x ∂volume.restrict (Ioo 0 L), p x := by
  rw [reflectedUniformLaw_eq_open,
    Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)]

def reflectedUniformToIntervalL2 (L : ℝ) (hL : 0 < L) :
    ReflectedUniformL2 L hL →L[ℝ] IntervalSobolevL2 0 L :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (reflectedVolume_eq_smul_uniform L hL).le

def reflectedIntervalToUniformL2 (L : ℝ) (hL : 0 < L) :
    IntervalSobolevL2 0 L →L[ℝ] ReflectedUniformL2 L hL :=
  Lp.LpToLpOfMeasureLeSMul
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hL).ne') (reflectedUniformLaw_eq_open L hL).le

theorem reflectedUniformToIntervalL2_coe (L : ℝ) (hL : 0 < L) (f : ReflectedUniformL2 L hL) :
    reflectedUniformToIntervalL2 L hL f =ᵐ[volume.restrict (Ioo 0 L)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

theorem reflectedIntervalToUniformL2_coe (L : ℝ) (hL : 0 < L) (f : IntervalSobolevL2 0 L) :
    reflectedIntervalToUniformL2 L hL f =ᵐ[reflectedUniformLaw L hL] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

theorem reflectedIntervalToUniformL2_left_inverse (L : ℝ) (hL : 0 < L)
    (f : ReflectedUniformL2 L hL) :
    reflectedIntervalToUniformL2 L hL (reflectedUniformToIntervalL2 L hL f) = f := by
  apply Lp.ext
  exact (reflectedIntervalToUniformL2_coe L hL _).trans
    ((reflectedUniformLaw_ae_iff L hL _).mpr (reflectedUniformToIntervalL2_coe L hL f))

theorem reflectedUniformToIntervalL2_right_inverse (L : ℝ) (hL : 0 < L)
    (f : IntervalSobolevL2 0 L) :
    reflectedUniformToIntervalL2 L hL (reflectedIntervalToUniformL2 L hL f) = f := by
  apply Lp.ext
  exact (reflectedUniformToIntervalL2_coe L hL _).trans
    ((reflectedUniformLaw_ae_iff L hL _).mp (reflectedIntervalToUniformL2_coe L hL f))

def reflectedUniformL2Equiv (L : ℝ) (hL : 0 < L) :
    ReflectedUniformL2 L hL ≃L[ℝ] IntervalSobolevL2 0 L where
  toLinearEquiv :=
    { (reflectedUniformToIntervalL2 L hL).toLinearMap with
      invFun := reflectedIntervalToUniformL2 L hL
      left_inv := reflectedIntervalToUniformL2_left_inverse L hL
      right_inv := reflectedUniformToIntervalL2_right_inverse L hL }
  continuous_toFun := (reflectedUniformToIntervalL2 L hL).continuous
  continuous_invFun := (reflectedIntervalToUniformL2 L hL).continuous

theorem reflectedUniformL2Equiv_coe (L : ℝ) (hL : 0 < L) (f : ReflectedUniformL2 L hL) :
    reflectedUniformL2Equiv L hL f =ᵐ[volume.restrict (Ioo 0 L)] f :=
  reflectedUniformToIntervalL2_coe L hL f

theorem reflectedUniformL2Equiv_symm_coe (L : ℝ) (hL : 0 < L) (f : IntervalSobolevL2 0 L) :
    (reflectedUniformL2Equiv L hL).symm f =ᵐ[reflectedUniformLaw L hL] f :=
  reflectedIntervalToUniformL2_coe L hL f

theorem reflectedUniformL2Equiv_inner (L : ℝ) (hL : 0 < L) (f g : ReflectedUniformL2 L hL) :
    inner ℝ (reflectedUniformL2Equiv L hL f) (reflectedUniformL2Equiv L hL g) =
      L * inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  have he : (∫ x, inner ℝ ((reflectedUniformL2Equiv L hL f) x)
      ((reflectedUniformL2Equiv L hL g) x) ∂volume.restrict (Ioo 0 L)) =
      ∫ x, inner ℝ (f x) (g x) ∂volume.restrict (Ioo 0 L) := by
    apply integral_congr_ae
    filter_upwards [reflectedUniformL2Equiv_coe L hL f, reflectedUniformL2Equiv_coe L hL g]
      with x hf hg
    rw [hf, hg]
  rw [he, reflectedVolume_eq_smul_uniform L hL, integral_smul_measure,
    ENNReal.toReal_ofReal hL.le, smul_eq_mul]

theorem reflectedUniformL2Equiv_norm_sq (L : ℝ) (hL : 0 < L) (f : ReflectedUniformL2 L hL) :
    ‖reflectedUniformL2Equiv L hL f‖ ^ 2 = L * ‖f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using reflectedUniformL2Equiv_inner L hL f f

end TimeTraps.Probability

end
