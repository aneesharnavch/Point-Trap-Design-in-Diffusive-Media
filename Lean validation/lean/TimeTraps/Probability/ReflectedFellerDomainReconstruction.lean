module

public import TimeTraps.Probability.ReflectedFellerNeumannGenerator

@[expose] public section

/-! Every continuous zero-mean curvature reconstructs a genuine C²
Neumann function by two ordinary integrations. Endpoint slope conditions
are derived, including the right endpoint from the vanishing mean. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set

def reflectedFellerRawPrimitive (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) : ℝ :=
  ∫ y in 0..x, reflectedFellerExtension L hL q y

theorem reflectedFellerRawPrimitive_derivative (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    HasDerivAt (reflectedFellerRawPrimitive L hL q) (reflectedFellerExtension L hL q x) x := by
  have hc := (reflectedFellerExtension L hL q).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem reflectedFellerRawPrimitive_continuous (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) : Continuous (reflectedFellerRawPrimitive L hL q) :=
  continuous_iff_continuousAt.mpr (fun x => (reflectedFellerRawPrimitive_derivative L hL q x).continuousAt)

def reflectedNeumannOfCurvature (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (hq : reflectedFellerMean L hL q = 0) (c : ℝ) :
    ReflectedNeumannC2 L where
  value x := reflectedFellerRawPrimitive L hL (reflectedFellerPrimitive L hL q) x + c
  slope := reflectedFellerRawPrimitive L hL q
  curvature := reflectedFellerExtension L hL q
  value_continuous := ((reflectedFellerRawPrimitive_continuous L hL _).add continuous_const).continuousOn
  slope_continuous := (reflectedFellerRawPrimitive_continuous L hL q).continuousOn
  curvature_continuous := (reflectedFellerExtension L hL q).continuous.continuousOn
  value_derivative x hx := by
    apply ((reflectedFellerRawPrimitive_derivative L hL _ x).add_const c).congr_deriv
    exact reflectedFellerExtension_on_interval L hL (reflectedFellerPrimitive L hL q)
      ⟨x, hx.1.le, hx.2.le⟩
  slope_derivative x _ := reflectedFellerRawPrimitive_derivative L hL q x
  neumann_left := by simp only [reflectedFellerRawPrimitive, intervalIntegral.integral_same]
  neumann_right := by
    rw [reflectedFellerMean_apply] at hq
    exact (mul_eq_zero.mp hq).resolve_left (inv_ne_zero hL.ne')

theorem reflectedNeumannOfCurvature_value (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (hq : reflectedFellerMean L hL q = 0) (c : ℝ) :
    (reflectedNeumannOfCurvature L hL q hq c).valueMap =
      reflectedFellerPrimitive L hL (reflectedFellerPrimitive L hL q) + c • 1 := by
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one]
  rfl

theorem reflectedNeumannOfCurvature_curvature (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) (hq : reflectedFellerMean L hL q = 0) (c : ℝ) :
    (reflectedNeumannOfCurvature L hL q hq c).curvatureMap = q := by
  ext x
  exact reflectedFellerExtension_on_interval L hL q x

end TimeTraps.Probability

end
