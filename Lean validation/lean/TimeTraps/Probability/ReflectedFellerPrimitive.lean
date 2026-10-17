module

public import TimeTraps.Probability.ReflectedFellerGeneratorClosed
public import TimeTraps.Analysis.NeumannCosineDensity

@[expose] public section

/-! Bounded integration and mean removal on the actual continuous-function
space. The folded extension is used only to define ordinary integrals;
on the closed physical interval it is exactly the input function. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

def reflectedFellerPrimitiveValue (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) : C(Icc (0 : ℝ) L, ℝ) where
  toFun x := ∫ y in 0..x.val, reflectedFellerExtension L hL f y
  continuous_toFun := by
    have hc := (reflectedFellerExtension L hL f).continuous
    have hp : Continuous (fun x : ℝ => ∫ y in 0..x, reflectedFellerExtension L hL f y) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
        hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt
    exact hp.comp continuous_subtype_val

theorem reflectedFellerPrimitiveValue_norm (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) : ‖reflectedFellerPrimitiveValue L hL f‖ ≤ L * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hL.le (norm_nonneg f))).mpr
  intro x
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x.val)
    (fun y _ => reflectedFellerExtension_bound L hL f y)
  change ‖∫ y in 0..x.val, reflectedFellerExtension L hL f y‖ ≤ L * ‖f‖
  calc
    _ ≤ ‖f‖ * |x.val - 0| := hb
    _ = x.val * ‖f‖ := by rw [sub_zero, abs_of_nonneg x.property.1, mul_comm]
    _ ≤ L * ‖f‖ := mul_le_mul_of_nonneg_right x.property.2 (norm_nonneg f)

def reflectedFellerPrimitiveLinear (L : ℝ) (hL : 0 < L) :
    C(Icc (0 : ℝ) L, ℝ) →ₗ[ℝ] C(Icc (0 : ℝ) L, ℝ) where
  toFun := reflectedFellerPrimitiveValue L hL
  map_add' f g := by
    ext x
    change (∫ y in 0..x.val, reflectedFellerExtension L hL f y + reflectedFellerExtension L hL g y) = _
    exact intervalIntegral.integral_add
      ((reflectedFellerExtension L hL f).continuous.intervalIntegrable 0 x.val)
      ((reflectedFellerExtension L hL g).continuous.intervalIntegrable 0 x.val)
  map_smul' c f := by
    ext x
    change (∫ y in 0..x.val, c • reflectedFellerExtension L hL f y) = _
    exact intervalIntegral.integral_smul c _

def reflectedFellerPrimitive (L : ℝ) (hL : 0 < L) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) :=
  (reflectedFellerPrimitiveLinear L hL).mkContinuous L
    (reflectedFellerPrimitiveValue_norm L hL)

theorem reflectedFellerPrimitive_apply (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) :
    reflectedFellerPrimitive L hL f x = ∫ y in 0..x.val, reflectedFellerExtension L hL f y := rfl

theorem reflectedFellerPrimitive_norm (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) : ‖reflectedFellerPrimitive L hL f‖ ≤ L * ‖f‖ :=
  reflectedFellerPrimitiveValue_norm L hL f

def reflectedFellerMean (L : ℝ) (hL : 0 < L) : C(Icc (0 : ℝ) L, ℝ) →L[ℝ] ℝ :=
  L⁻¹ • ((ContinuousMap.evalCLM ℝ ⟨L, hL.le, le_rfl⟩).comp (reflectedFellerPrimitive L hL))

theorem reflectedFellerMean_apply (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerMean L hL f = L⁻¹ * ∫ y in 0..L, reflectedFellerExtension L hL f y := rfl

def reflectedFellerMeanZero (L : ℝ) (hL : 0 < L) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) :=
  ContinuousLinearMap.id ℝ _ - (reflectedFellerMean L hL).smulRight 1

theorem reflectedFellerMeanZero_apply (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerMeanZero L hL f = f - reflectedFellerMean L hL f • 1 := rfl

theorem reflectedFellerMean_one (L : ℝ) (hL : 0 < L) :
    reflectedFellerMean L hL 1 = 1 := by
  rw [reflectedFellerMean_apply]
  change L⁻¹ * (∫ _y in (0 : ℝ)..L, (1 : ℝ)) = 1
  simp [hL.ne']

theorem reflectedFellerMeanZero_one (L : ℝ) (hL : 0 < L) :
    reflectedFellerMeanZero L hL 1 = 0 := by
  rw [reflectedFellerMeanZero_apply, reflectedFellerMean_one, one_smul, sub_self]

theorem reflectedFellerPrimitive_of_derivative (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt F (reflectedFellerExtension L hL f x) x)
    (x : Icc (0 : ℝ) L) :
    reflectedFellerPrimitive L hL f x = F x.val - F 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.property.1
  · exact hF.mono (Icc_subset_Icc le_rfl x.property.2)
  · intro y hy
    exact hd y ⟨hy.1, hy.2.trans_le x.property.2⟩
  · exact (reflectedFellerExtension L hL f).continuous.intervalIntegrable 0 x.val

end TimeTraps.Probability

end
