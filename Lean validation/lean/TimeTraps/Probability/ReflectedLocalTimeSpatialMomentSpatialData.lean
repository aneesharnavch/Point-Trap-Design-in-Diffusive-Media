module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentHalfVersion
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentParameterInverse

@[expose] public section

/-! The two continuous half-line versions are joined at their common
midpoint. The result is continuous in the spatial level on every sample,
strongly measurable at each level, and agrees almost surely with the
original C([0,T])-valued local time at every fixed level. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedLocalTimeSpatialVersion (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) := by
  classical
  exact if reflectedLocalTimeHalfVersion L hL D hD x T false 0 ω =
      reflectedLocalTimeHalfVersion L hL D hD x T true 0 ω then
    if a.val ≤ L / 2 then reflectedLocalTimeHalfVersion L hL D hD x T false (reflectedSpatialLeftInverse L a) ω
      else reflectedLocalTimeHalfVersion L hL D hD x T true (reflectedSpatialRightInverse L a) ω
    else 0

theorem reflectedLocalTimeSpatialVersion_continuous (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun a => reflectedLocalTimeSpatialVersion L hL D hD x T a ω) := by
  by_cases hm : reflectedLocalTimeHalfVersion L hL D hD x T false 0 ω =
      reflectedLocalTimeHalfVersion L hL D hD x T true 0 ω
  · simp only [reflectedLocalTimeSpatialVersion, if_pos hm]
    apply Continuous.if_le
      ((reflectedLocalTimeHalfVersion_continuous L hL D hD x T false ω).comp
        (reflectedSpatialLeftInverse_continuous L))
      ((reflectedLocalTimeHalfVersion_continuous L hL D hD x T true ω).comp
        (reflectedSpatialRightInverse_continuous L)) continuous_subtype_val continuous_const
    intro a ha
    obtain ⟨hl, hr⟩ := reflectedSpatialInverse_midpoint L hL a ha
    change reflectedLocalTimeHalfVersion L hL D hD x T false (reflectedSpatialLeftInverse L a) ω =
      reflectedLocalTimeHalfVersion L hL D hD x T true (reflectedSpatialRightInverse L a) ω
    rw [hl, hr]
    exact hm
  · simp only [reflectedLocalTimeSpatialVersion, if_neg hm]
    exact continuous_const

end TimeTraps.Probability
