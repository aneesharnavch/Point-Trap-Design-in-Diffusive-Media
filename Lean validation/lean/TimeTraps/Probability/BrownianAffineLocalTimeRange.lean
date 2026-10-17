module

public import TimeTraps.Probability.BrownianAffineLocalTimeStieltjes
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! The actual affine path has compact range on every finite horizon.
At a fixed level outside that range, compactness gives a positive distance
from the level, so both local-time normalizations vanish throughout the
horizon on the previously constructed fixed-level support event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

def affineBrownianPathRange (x σ : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : Set ℝ :=
  (fun t => affineBrownianInput x σ t ω) '' Icc 0 T

theorem affineBrownianInput_continuous (x σ : ℝ) {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω) : Continuous (fun t => affineBrownianInput x σ t ω) :=
  continuous_const.add (continuous_const.mul (BrownianDyadicRegular.continuous hω))

theorem affineBrownianPathRange_compact (x σ : ℝ) (T : ℝ≥0) {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω) : IsCompact (affineBrownianPathRange x σ T ω) :=
  isCompact_Icc.image (affineBrownianInput_continuous x σ hω)

theorem affineBrownianLocalTime_vanishes_outside_range {x σ a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hω : affineBrownianLocalTimeRegular x σ a ω) (T : ℝ≥0)
    (ha : a ∉ affineBrownianPathRange x σ T ω) :
    ∀ s ∈ Icc (0 : ℝ≥0) T,
      affineBrownianTanakaCorrection x σ a s ω = 0 ∧
        affineBrownianOccupationDensity x σ a s ω = 0 := by
  have hb : Continuous (fun s => |brownianDyadicPath s ω - (a - x) / σ|) :=
    ((BrownianDyadicRegular.continuous hω.2.1).sub continuous_const).abs
  have hp : ∀ s ∈ Icc (0 : ℝ≥0) T, 0 < |brownianDyadicPath s ω - (a - x) / σ| := by
    intro s hs
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    intro he
    exact ha ⟨s, hs, (affineBrownianInput_eq_level_iff x hσ a s ω).mpr he⟩
  obtain ⟨δ, hδ, hdist⟩ := isCompact_Icc.exists_forall_le' hb.continuousOn hp
  have hf := brownianLocalTimeSupportRegular_flat_real hω.2 (show (0 : ℝ≥0) ≤ T from zero_le)
    hδ hdist
  intro s hs
  have hz : brownianLocalTimeGlobalPath ((a - x) / σ) s ω = 0 := by
    rw [hf s hs, brownianLocalTimeGlobalPath_zero]
  rw [(affineBrownianLocalTimeRegular_values hω s).1,
    (affineBrownianLocalTimeRegular_values hω s).2, hz]
  exact ⟨mul_zero _, mul_zero _⟩

end TimeTraps.Probability
