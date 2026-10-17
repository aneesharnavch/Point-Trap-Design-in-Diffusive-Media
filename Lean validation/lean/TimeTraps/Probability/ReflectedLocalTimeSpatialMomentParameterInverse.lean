module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentParameters

@[expose] public section

/-! Continuous inverse parameters on the two halves of the open spatial
interval, including their shared midpoint. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedSpatialLeftInverse (L : ℝ) (a : Ioo (0 : ℝ) L) : ℝ≥0 :=
  (L / a.val - 2).toNNReal

noncomputable def reflectedSpatialRightInverse (L : ℝ) (a : Ioo (0 : ℝ) L) : ℝ≥0 :=
  (L / (L - a.val) - 2).toNNReal

theorem reflectedSpatialLeftInverse_continuous (L : ℝ) : Continuous (reflectedSpatialLeftInverse L) :=
  continuous_real_toNNReal.comp ((continuous_const.div continuous_subtype_val
    (fun a => ne_of_gt a.property.1)).sub continuous_const)

theorem reflectedSpatialRightInverse_continuous (L : ℝ) : Continuous (reflectedSpatialRightInverse L) :=
  continuous_real_toNNReal.comp ((continuous_const.div (continuous_const.sub continuous_subtype_val)
    (fun a => sub_ne_zero.mpr (ne_of_gt a.property.2))).sub continuous_const)

theorem reflectedSpatialLeftParameter_inverse (L : ℝ) (hL : 0 < L) (a : Ioo (0 : ℝ) L)
    (ha : a.val ≤ L / 2) : reflectedSpatialLeftParameter L hL (reflectedSpatialLeftInverse L a) = a := by
  apply Subtype.ext
  have hn : 0 ≤ L / a.val - 2 := sub_nonneg.mpr ((le_div_iff₀ a.property.1).mpr (by linarith))
  change L / (((L / a.val - 2).toNNReal : ℝ) + 2) = a.val
  rw [Real.coe_toNNReal _ hn]
  have he : L / a.val - 2 + 2 = L / a.val := by ring
  rw [he, div_div_cancel₀ hL.ne']

theorem reflectedSpatialRightParameter_inverse (L : ℝ) (hL : 0 < L) (a : Ioo (0 : ℝ) L)
    (ha : L / 2 ≤ a.val) : reflectedSpatialRightParameter L hL (reflectedSpatialRightInverse L a) = a := by
  apply Subtype.ext
  have hd : 0 < L - a.val := sub_pos.mpr a.property.2
  have hn : 0 ≤ L / (L - a.val) - 2 := sub_nonneg.mpr ((le_div_iff₀ hd).mpr (by linarith))
  change L - L / (((L / (L - a.val) - 2).toNNReal : ℝ) + 2) = a.val
  rw [Real.coe_toNNReal _ hn]
  have he : L / (L - a.val) - 2 + 2 = L / (L - a.val) := by ring
  rw [he, div_div_cancel₀ hL.ne']
  ring

theorem reflectedSpatialInverse_midpoint (L : ℝ) (hL : 0 < L) (a : Ioo (0 : ℝ) L)
    (ha : a.val = L / 2) : reflectedSpatialLeftInverse L a = 0 ∧ reflectedSpatialRightInverse L a = 0 := by
  have hleft : L / a.val = 2 := by rw [ha]; field_simp
  have hright : L / (L - a.val) = 2 := by rw [ha]; field_simp; norm_num
  change (L / a.val - 2).toNNReal = 0 ∧ (L / (L - a.val) - 2).toNNReal = 0
  simp only [hleft, hright, sub_self, Real.toNNReal_zero, and_self]

end TimeTraps.Probability
