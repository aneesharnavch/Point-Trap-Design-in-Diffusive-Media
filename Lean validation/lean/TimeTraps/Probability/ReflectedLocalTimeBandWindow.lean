module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeMaximal

@[expose] public section

/-! A fixed compact interior window around the level of interest. The
clipping map is continuous and is the identity on every sufficiently
narrow occupation band. It is used only to extend the L2 error family. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology

noncomputable def reflectedBandClippedLevel {L : ℝ} (a : Ioo (0 : ℝ) L) (b : ℝ) : Ioo (0 : ℝ) L :=
  ⟨max (a.val / 2) (min ((a.val + L) / 2) b),
    lt_of_lt_of_le (by linarith [a.property.1]) (le_max_left _ _),
    lt_of_le_of_lt (max_le (by linarith [a.property.1, a.property.2]) (min_le_left _ _))
      (by linarith [a.property.2])⟩

theorem reflectedBandClippedLevel_continuous {L : ℝ} (a : Ioo (0 : ℝ) L) :
    Continuous (reflectedBandClippedLevel a) :=
  (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem reflectedBandClippedLevel_center {L : ℝ} (a : Ioo (0 : ℝ) L) :
    reflectedBandClippedLevel a a.val = a := by
  apply Subtype.ext
  change max (a.val / 2) (min ((a.val + L) / 2) a.val) = a.val
  rw [min_eq_right (by linarith [a.property.2]), max_eq_right (by linarith [a.property.1])]

theorem reflectedBandClippedLevel_eq {L : ℝ} (a : Ioo (0 : ℝ) L) {b : ℝ}
    (hb : b ∈ Icc (a.val / 2) ((a.val + L) / 2)) : (reflectedBandClippedLevel a b).val = b := by
  change max (a.val / 2) (min ((a.val + L) / 2) b) = b
  rw [min_eq_right hb.2, max_eq_right hb.1]

theorem reflectedBandClippedLevel_eq_on_band {L : ℝ} (a : Ioo (0 : ℝ) L) {h b : ℝ}
    (hh : h < min (a.val / 2) ((L - a.val) / 2)) (hb : b ∈ Ioo (a.val - h) (a.val + h)) :
    (reflectedBandClippedLevel a b).val = b := by
  apply reflectedBandClippedLevel_eq
  constructor
  · linarith [(lt_min_iff.mp hh).1, hb.1]
  · linarith [(lt_min_iff.mp hh).2, hb.2]

theorem reflectedBandWindow_radius_pos {L : ℝ} (a : Ioo (0 : ℝ) L) :
    0 < min (a.val / 2) ((L - a.val) / 2) := by
  apply lt_min
  · linarith [a.property.1]
  · linarith [a.property.2]

end TimeTraps.Probability
