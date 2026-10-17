module

public import TimeTraps.Probability.ReflectedNeumannC2ExtensionIdentity

@[expose] public section

/-! The actual folded extension of every C² Neumann interval function is
globally C². Its second derivative is exactly the folded curvature and
is globally bounded by the curvature's interval uniform norm. The proof
identifies this extension with a global double primitive, including all
fold corners; no extra endpoint curvature condition is imposed. -/

namespace TimeTraps.Probability

open MeasureTheory Set

theorem ReflectedNeumannC2.extension_eq_doublePrimitive {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) :
    (reflectedFellerExtension L hL F.valueMap : ℝ → ℝ) =
      fun x => reflectedNeumannDoublePrimitive L hL F.curvatureMap x + F.value 0 := by
  have hp : reflectedFellerNeumannPrimitive L hL F.curvatureMap = F.valueMap - F.value 0 • 1 := by
    rw [reflectedFellerNeumannPrimitive_apply, F.meanZero_curvature hL, F.double_primitive hL]
  funext x
  have he := reflectedFellerNeumannPrimitive_extension L hL F.curvatureMap x
  rw [hp, F.meanZero_curvature hL] at he
  change F.valueMap (reflectedIntervalFold L hL x) - F.value 0 * 1 =
    reflectedNeumannDoublePrimitive L hL F.curvatureMap x at he
  change F.valueMap (reflectedIntervalFold L hL x) =
    reflectedNeumannDoublePrimitive L hL F.curvatureMap x + F.value 0
  linarith

theorem ReflectedNeumannC2.extension_global_derivative {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (x : ℝ) :
    HasDerivAt (reflectedFellerExtension L hL F.valueMap)
      (reflectedFellerRawPrimitive L hL F.curvatureMap x) x := by
  rw [F.extension_eq_doublePrimitive hL]
  exact (reflectedNeumannDoublePrimitive_derivative L hL F.curvatureMap x).add_const (F.value 0)

theorem ReflectedNeumannC2.extension_global_contDiff {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) : ContDiff ℝ 2 (reflectedFellerExtension L hL F.valueMap : ℝ → ℝ) := by
  rw [F.extension_eq_doublePrimitive hL]
  exact (reflectedNeumannDoublePrimitive_contDiff L hL F.curvatureMap).add contDiff_const

theorem ReflectedNeumannC2.extension_global_second {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (x : ℝ) :
    deriv (deriv (reflectedFellerExtension L hL F.valueMap)) x =
      reflectedFellerExtension L hL F.curvatureMap x := by
  have he : deriv (reflectedFellerExtension L hL F.valueMap) =
      reflectedFellerRawPrimitive L hL F.curvatureMap :=
    funext (fun y => (F.extension_global_derivative hL y).deriv)
  rw [he]
  exact (reflectedFellerRawPrimitive_derivative L hL F.curvatureMap x).deriv

theorem ReflectedNeumannC2.extension_global_second_bound {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (x : ℝ) :
    |deriv (deriv (reflectedFellerExtension L hL F.valueMap)) x| ≤ ‖F.curvatureMap‖ := by
  rw [F.extension_global_second hL x]
  exact reflectedFellerExtension_bound L hL F.curvatureMap x

end TimeTraps.Probability
