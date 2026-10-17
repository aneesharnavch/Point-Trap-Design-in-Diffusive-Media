module

public import TimeTraps.Probability.ReflectedFellerPrimitive

@[expose] public section

/-! The full C² Neumann test class is expressed by continuous value,
slope and curvature on the closed interval, and the two classical
derivative identities in its open interior. No differentiable extension
beyond either endpoint is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

structure ReflectedNeumannC2 (L : ℝ) where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  curvature : ℝ → ℝ
  value_continuous : ContinuousOn value (Icc 0 L)
  slope_continuous : ContinuousOn slope (Icc 0 L)
  curvature_continuous : ContinuousOn curvature (Icc 0 L)
  value_derivative : ∀ x ∈ Ioo 0 L, HasDerivAt value (slope x) x
  slope_derivative : ∀ x ∈ Ioo 0 L, HasDerivAt slope (curvature x) x
  neumann_left : slope 0 = 0
  neumann_right : slope L = 0

def ReflectedNeumannC2.valueMap {L : ℝ} (F : ReflectedNeumannC2 L) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun x => F.value x.val, F.value_continuous.domRestrict⟩

def ReflectedNeumannC2.slopeMap {L : ℝ} (F : ReflectedNeumannC2 L) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun x => F.slope x.val, F.slope_continuous.domRestrict⟩

def ReflectedNeumannC2.curvatureMap {L : ℝ} (F : ReflectedNeumannC2 L) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun x => F.curvature x.val, F.curvature_continuous.domRestrict⟩

theorem ReflectedNeumannC2.primitive_curvature {L : ℝ} (F : ReflectedNeumannC2 L) (hL : 0 < L) :
    reflectedFellerPrimitive L hL F.curvatureMap = F.slopeMap := by
  ext x
  change reflectedFellerPrimitive L hL F.curvatureMap x = F.slope x.val
  have he := reflectedFellerPrimitive_of_derivative L hL F.curvatureMap F.slope
    F.slope_continuous (fun y hy => by
      rw [reflectedFellerExtension_on_interval L hL _ ⟨y, hy.1.le, hy.2.le⟩]
      exact F.slope_derivative y hy) x
  simpa only [F.neumann_left, sub_zero] using he

theorem ReflectedNeumannC2.primitive_slope {L : ℝ} (F : ReflectedNeumannC2 L) (hL : 0 < L) :
    reflectedFellerPrimitive L hL F.slopeMap = F.valueMap - F.value 0 • 1 := by
  ext x
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one]
  change reflectedFellerPrimitive L hL F.slopeMap x = F.value x.val - F.value 0
  have he := reflectedFellerPrimitive_of_derivative L hL F.slopeMap F.value
    F.value_continuous (fun y hy => by
      rw [reflectedFellerExtension_on_interval L hL _ ⟨y, hy.1.le, hy.2.le⟩]
      exact F.value_derivative y hy) x
  exact he

theorem ReflectedNeumannC2.mean_curvature {L : ℝ} (F : ReflectedNeumannC2 L) (hL : 0 < L) :
    reflectedFellerMean L hL F.curvatureMap = 0 := by
  change L⁻¹ * reflectedFellerPrimitive L hL F.curvatureMap ⟨L, hL.le, le_rfl⟩ = 0
  rw [F.primitive_curvature hL]
  change L⁻¹ * F.slope L = 0
  rw [F.neumann_right, mul_zero]

theorem ReflectedNeumannC2.meanZero_curvature {L : ℝ} (F : ReflectedNeumannC2 L) (hL : 0 < L) :
    reflectedFellerMeanZero L hL F.curvatureMap = F.curvatureMap := by
  rw [reflectedFellerMeanZero_apply, F.mean_curvature hL, zero_smul, sub_zero]

theorem ReflectedNeumannC2.double_primitive {L : ℝ} (F : ReflectedNeumannC2 L) (hL : 0 < L) :
    reflectedFellerPrimitive L hL (reflectedFellerPrimitive L hL F.curvatureMap) =
      F.valueMap - F.value 0 • 1 := by
  rw [F.primitive_curvature hL, F.primitive_slope hL]

end TimeTraps.Probability

end
