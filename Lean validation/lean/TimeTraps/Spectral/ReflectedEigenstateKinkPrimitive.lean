module

public import TimeTraps.Probability.ReflectedNeumannC2ExtensionPrimitive

@[expose] public section

/-! The absolute-value Green potential of continuous interval data is a
global C² double primitive plus an affine function on the physical interval.
The extension outside the interval is used only for the global C² base. -/

noncomputable section

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Probability

theorem reflectedEigenstate_abs_integral (L : ℝ) (hL : 0 < L)
    (q : C(Icc (0 : ℝ) L, ℝ)) {y : ℝ} (hy : y ∈ Icc 0 L) :
    (∫ z in 0..L, reflectedFellerExtension L hL q z * |z - y|) =
      (L - y) * reflectedFellerRawPrimitive L hL q L -
        reflectedNeumannDoublePrimitive L hL q L +
          2 * reflectedNeumannDoublePrimitive L hL q y := by
  let R := reflectedFellerRawPrimitive L hL q
  let Q := reflectedNeumannDoublePrimitive L hL q
  let f := reflectedFellerExtension L hL q
  have hR (z : ℝ) : HasDerivAt R (f z) z := reflectedFellerRawPrimitive_derivative L hL q z
  have hQ (z : ℝ) : HasDerivAt Q (R z) z := reflectedNeumannDoublePrimitive_derivative L hL q z
  have hR0 : R 0 = 0 := by simp [R, reflectedFellerRawPrimitive]
  have hQ0 : Q 0 = 0 := by simp [Q, reflectedNeumannDoublePrimitive]
  have hl : (∫ z in 0..y, f z * (y - z)) = Q y := by
    have hd (z : ℝ) : HasDerivAt (fun z => R z * (y - z) + Q z) (f z * (y - z)) z := by
      convert ((hR z).mul ((hasDerivAt_const z y).sub (hasDerivAt_id z))).add (hQ z) using 1 <;>
        first | rfl | (dsimp only [Pi.sub_apply, id_eq]; ring)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _ => hd z) ((f.continuous.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 y)
    simpa only [sub_self, mul_zero, hR0, hQ0, zero_mul, add_zero, zero_add, sub_zero] using he
  have hr : (∫ z in y..L, f z * (z - y)) = (L - y) * R L - Q L + Q y := by
    have hd (z : ℝ) : HasDerivAt (fun z => R z * (z - y) - Q z) (f z * (z - y)) z := by
      convert ((hR z).mul ((hasDerivAt_id z).sub_const y)).sub (hQ z) using 1 <;>
        first | rfl | (dsimp only [Pi.sub_apply, id_eq]; ring)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _ => hd z) ((f.continuous.mul (continuous_id.sub continuous_const)).intervalIntegrable y L)
    simp only [sub_self, mul_zero, zero_sub] at he
    calc
      _ = (R L * (L - y) - Q L) - -Q y := he
      _ = _ := by ring
  have hc : Continuous (fun z => f z * |z - y|) :=
    f.continuous.mul (continuous_id.sub continuous_const).abs
  change (∫ z in 0..L, f z * |z - y|) = (L - y) * R L - Q L + 2 * Q y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 y)
    (hc.intervalIntegrable y L)]
  have hleft : (∫ z in 0..y, f z * |z - y|) = Q y := by
    rw [← hl]
    apply intervalIntegral.integral_congr_Ioo_of_le hy.1
    intro z hz
    dsimp only
    rw [abs_of_neg (sub_neg.mpr hz.2)]
    ring
  have hright : (∫ z in y..L, f z * |z - y|) = (L - y) * R L - Q L + Q y := by
    rw [← hr]
    apply intervalIntegral.integral_congr_Ioo_of_le hy.2
    intro z hz
    dsimp only
    rw [abs_of_pos (sub_pos.mpr hz.1)]
  rw [hleft, hright]
  ring

end TimeTraps.Spectral

end
