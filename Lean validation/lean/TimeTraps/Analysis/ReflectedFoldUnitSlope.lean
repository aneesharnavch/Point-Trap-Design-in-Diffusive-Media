module

public import TimeTraps.Analysis.ReflectedFoldSlopeRegularity

@[expose] public section

/-! A Borel unit-valued representative of the fold slope, assigning +1
at every corner. It agrees with the original slope off the corner lattice.
The corner convention makes the first deterministic grid coefficient unit
even when the initial position is a corner. -/

noncomputable section

namespace TimeTraps.Analysis

open Set Filter MeasureTheory
open scoped Topology

def reflectedFoldUnitSlope (L z : ℝ) : ℝ :=
  if reflectedFoldSlope L z = 0 then 1 else reflectedFoldSlope L z

theorem reflectedFoldUnitSlope_measurable (L : ℝ) (hL : 0 < L) :
    Measurable (reflectedFoldUnitSlope L) :=
  measurable_const.ite (measurableSet_eq_fun (reflectedFoldSlope_measurable L hL) measurable_const)
    (reflectedFoldSlope_measurable L hL)

theorem reflectedFoldUnitSlope_eq (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) : reflectedFoldUnitSlope L z = reflectedFoldSlope L z := by
  have hs := reflectedFoldSlope_square_eq_one L hL z hz
  have hn : reflectedFoldSlope L z ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  exact if_neg hn

theorem reflectedFoldUnitSlope_eq_one_or_neg_one (L : ℝ) (hL : 0 < L) (z : ℝ) :
    reflectedFoldUnitSlope L z = 1 ∨ reflectedFoldUnitSlope L z = -1 := by
  by_cases hc : ∃ j : ℤ, z = j * L
  · obtain ⟨j, rfl⟩ := hc
    left
    simp [reflectedFoldUnitSlope, reflectedFoldSlope_int_corner L hL j]
  · have hz : ∀ j : ℤ, z ≠ j * L := by simpa only [not_exists] using hc
    obtain ⟨c, hc, he, _⟩ := reflectedFoldSlope_locally_signed L hL z hz
    rw [reflectedFoldUnitSlope_eq L hL z hz, he]
    exact hc

theorem reflectedFoldUnitSlope_abs (L : ℝ) (hL : 0 < L) (z : ℝ) :
    |reflectedFoldUnitSlope L z| = 1 := by
  rcases reflectedFoldUnitSlope_eq_one_or_neg_one L hL z with he | he <;> rw [he] <;> norm_num

theorem reflectedFoldUnitSlope_square (L : ℝ) (hL : 0 < L) (z : ℝ) :
    reflectedFoldUnitSlope L z ^ 2 = 1 := by
  rcases reflectedFoldUnitSlope_eq_one_or_neg_one L hL z with he | he <;> rw [he] <;> norm_num

theorem reflectedFoldUnitSlope_corner (L : ℝ) (hL : 0 < L) (j : ℤ) :
    reflectedFoldUnitSlope L (j * L) = 1 := by
  simp [reflectedFoldUnitSlope, reflectedFoldSlope_int_corner L hL j]

theorem reflectedFoldUnitSlope_continuousAt (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) : ContinuousAt (reflectedFoldUnitSlope L) z := by
  have he : reflectedFoldUnitSlope L =ᶠ[𝓝 z] (fun _ => reflectedFoldUnitSlope L z) := by
    filter_upwards [reflectedFoldSlope_locally_constant L hL z hz] with w hw
    unfold reflectedFoldUnitSlope
    rw [hw]
  exact continuousAt_const.congr_of_eventuallyEq he

end TimeTraps.Analysis

end
