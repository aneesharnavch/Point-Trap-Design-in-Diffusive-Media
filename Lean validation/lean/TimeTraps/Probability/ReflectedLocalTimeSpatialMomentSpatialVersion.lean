module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentSpatialMeasurable

@[expose] public section

/-! The two continuous half-line versions are joined at their common
midpoint. The result is continuous in the spatial level on every sample,
strongly measurable at each level, and agrees almost surely with the
original C([0,T])-valued local time at every fixed level. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedLocalTimeSpatialVersion_ae_eq (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    reflectedLocalTimeSpatialVersion L hL D hD x T a =ᵐ[brownianDyadicMeasure]
      reflectedLocalTimeCompactPath L hL D hD x T a.val := by
  by_cases ha : a.val ≤ L / 2
  · filter_upwards [reflectedLocalTimeHalfVersion_midpoint_ae L hL D hD x T,
      reflectedLocalTimeHalfVersion_ae_eq L hL D hD x T false (reflectedSpatialLeftInverse L a)] with ω hm he
    simp only [reflectedLocalTimeSpatialVersion, if_pos hm, if_pos ha, he]
    change reflectedLocalTimeCompactPath L hL D hD x T
      (reflectedSpatialLeftParameter L hL (reflectedSpatialLeftInverse L a)).val ω = _
    rw [reflectedSpatialLeftParameter_inverse L hL a ha]
  · filter_upwards [reflectedLocalTimeHalfVersion_midpoint_ae L hL D hD x T,
      reflectedLocalTimeHalfVersion_ae_eq L hL D hD x T true (reflectedSpatialRightInverse L a)] with ω hm he
    simp only [reflectedLocalTimeSpatialVersion, if_pos hm, if_neg ha, he]
    change reflectedLocalTimeCompactPath L hL D hD x T
      (reflectedSpatialRightParameter L hL (reflectedSpatialRightInverse L a)).val ω = _
    rw [reflectedSpatialRightParameter_inverse L hL a (le_of_not_ge ha)]

theorem reflectedLocalTimeSpatialVersion_fixed_level_all_times (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
      reflectedLocalTimeSpatialVersion L hL D hD x T a ω t =
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω := by
  filter_upwards [reflectedLocalTimeSpatialVersion_ae_eq L hL D hD x T a,
    reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a.val] with ω he hr t
  rw [he]
  exact reflectedLocalTimeCompactPath_apply L hL D hD x T a.val hr t

end TimeTraps.Probability
