module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentCompact

@[expose] public section

/-! Two continuous half-line parameterizations cover the entire open
spatial interval. Each is globally Lipschitz, avoiding any assertion of
local-time regularity at reflecting endpoints. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedSpatialLeftParameter (L : ℝ) (hL : 0 < L) (t : ℝ≥0) : Ioo (0 : ℝ) L :=
  by
    have ht : 0 ≤ t.val := t.property
    refine ⟨L / (t.val + 2), div_pos hL (by linarith), ?_⟩
    apply (div_lt_iff₀ (by linarith : 0 < t.val + 2)).mpr
    nlinarith [mul_nonneg hL.le ht]

noncomputable def reflectedSpatialRightParameter (L : ℝ) (hL : 0 < L) (t : ℝ≥0) : Ioo (0 : ℝ) L :=
  ⟨L - (reflectedSpatialLeftParameter L hL t).val,
    by linarith [(reflectedSpatialLeftParameter L hL t).property.2],
    by linarith [(reflectedSpatialLeftParameter L hL t).property.1]⟩

noncomputable def reflectedSpatialParameter (L : ℝ) (hL : 0 < L) (right : Bool) (t : ℝ≥0) : Ioo (0 : ℝ) L :=
  if right then reflectedSpatialRightParameter L hL t else reflectedSpatialLeftParameter L hL t

theorem reflectedSpatialLeftParameter_lipschitz_bound (L : ℝ) (hL : 0 < L) (s t : ℝ≥0) :
    |(reflectedSpatialLeftParameter L hL s).val - (reflectedSpatialLeftParameter L hL t).val| ≤
      L * dist s t := by
  have hs0 : 0 ≤ s.val := s.property
  have ht0 : 0 ≤ t.val := t.property
  have hs : 0 < s.val + 2 := by linarith
  have ht : 0 < t.val + 2 := by linarith
  have hd : 1 ≤ (s.val + 2) * (t.val + 2) := by nlinarith [mul_nonneg hs0 ht0]
  have he : L / (s.val + 2) - L / (t.val + 2) =
      L * (t.val - s.val) / ((s.val + 2) * (t.val + 2)) := by
    field_simp
    ring
  change |L / (s.val + 2) - L / (t.val + 2)| ≤ L * |s.val - t.val|
  rw [he, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (mul_pos hs ht), abs_sub_comm t.val s.val]
  exact div_le_self (by positivity) hd

theorem reflectedSpatialParameter_lipschitz_bound (L : ℝ) (hL : 0 < L) (right : Bool) (s t : ℝ≥0) :
    |(reflectedSpatialParameter L hL right s).val - (reflectedSpatialParameter L hL right t).val| ≤
      L * dist s t := by
  cases right
  · exact reflectedSpatialLeftParameter_lipschitz_bound L hL s t
  · change |(L - (reflectedSpatialLeftParameter L hL s).val) -
      (L - (reflectedSpatialLeftParameter L hL t).val)| ≤ _
    rw [show (L - (reflectedSpatialLeftParameter L hL s).val) -
      (L - (reflectedSpatialLeftParameter L hL t).val) =
      -((reflectedSpatialLeftParameter L hL s).val - (reflectedSpatialLeftParameter L hL t).val) by ring, abs_neg]
    exact reflectedSpatialLeftParameter_lipschitz_bound L hL s t

theorem reflectedSpatialParameter_zero (L : ℝ) (hL : 0 < L) (right : Bool) :
    (reflectedSpatialParameter L hL right 0).val = L / 2 := by
  cases right
  · change L / ((0 : ℝ≥0).val + 2) = L / 2
    norm_num
  · change L - L / ((0 : ℝ≥0).val + 2) = L / 2
    have hz : ((0 : ℝ≥0).val : ℝ) = 0 := rfl
    rw [hz, zero_add]
    ring

end TimeTraps.Probability
