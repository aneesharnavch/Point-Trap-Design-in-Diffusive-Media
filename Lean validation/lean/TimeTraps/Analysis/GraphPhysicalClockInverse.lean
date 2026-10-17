module

public import TimeTraps.Analysis.GraphPhysicalClockBounds
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Order.MonotoneContinuity

@[expose] public section

/-! The actual positive integral clock is an order isomorphism of
nonnegative time. Its inverse is continuous, strictly increasing and
satisfies quantitative bounds from the original speed bounds. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped NNReal Topology

noncomputable def GraphPhysicalClockSpeed.orderIso (v : GraphPhysicalClockSpeed) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective v.clock v.clock_strictMono v.clock_surjective

noncomputable def GraphPhysicalClockSpeed.inverse (v : GraphPhysicalClockSpeed) (t : ℝ≥0) : ℝ≥0 :=
  v.orderIso.symm t

theorem GraphPhysicalClockSpeed.clock_inverse (v : GraphPhysicalClockSpeed) (t : ℝ≥0) :
    v.clock (v.inverse t) = t :=
  v.orderIso.apply_symm_apply t

theorem GraphPhysicalClockSpeed.inverse_clock (v : GraphPhysicalClockSpeed) (s : ℝ≥0) :
    v.inverse (v.clock s) = s :=
  v.orderIso.symm_apply_apply s

theorem GraphPhysicalClockSpeed.inverse_zero (v : GraphPhysicalClockSpeed) : v.inverse 0 = 0 := by
  simpa only [v.clock_zero] using v.inverse_clock 0

theorem GraphPhysicalClockSpeed.inverse_strictMono (v : GraphPhysicalClockSpeed) : StrictMono v.inverse :=
  v.orderIso.symm.strictMono

theorem GraphPhysicalClockSpeed.inverse_continuous (v : GraphPhysicalClockSpeed) : Continuous v.inverse :=
  v.orderIso.symm.continuous

theorem GraphPhysicalClockSpeed.inverse_bounds (v : GraphPhysicalClockSpeed) (t : ℝ≥0) :
    t / v.upper ≤ v.inverse t ∧ v.inverse t ≤ t / v.lower := by
  have hu : 0 < v.upper := v.lower_pos.trans_le
    (show v.lower ≤ v.upper from (v.lower_le 0).trans (v.le_upper 0))
  have hb := v.clock_bounds (v.inverse t)
  rw [v.clock_inverse] at hb
  constructor
  · exact (div_le_iff₀ hu).mpr (by simpa only [mul_comm] using hb.2)
  · exact (le_div_iff₀ v.lower_pos).mpr (by simpa only [mul_comm] using hb.1)

theorem GraphPhysicalClockSpeed.inverse_increment_bounds (v : GraphPhysicalClockSpeed)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (t.val - s.val) / (v.upper : ℝ) ≤ (v.inverse t : ℝ) - (v.inverse s : ℝ) ∧
      (v.inverse t : ℝ) - (v.inverse s : ℝ) ≤ (t.val - s.val) / (v.lower : ℝ) := by
  have hu : (0 : ℝ) < v.upper :=
    lt_of_lt_of_le (v.rate_pos 0) (v.le_upper 0)
  have hb := v.clock_increment_bounds (v.inverse_strictMono.monotone hst)
  rw [v.clock_inverse, v.clock_inverse] at hb
  constructor
  · apply (div_le_iff₀ hu).mpr
    calc
      t.val - s.val ≤ (v.upper : ℝ) * ((v.inverse t : ℝ) - (v.inverse s : ℝ)) := hb.2
      _ = ((v.inverse t : ℝ) - (v.inverse s : ℝ)) * (v.upper : ℝ) := mul_comm _ _
  · apply (le_div_iff₀ (show (0 : ℝ) < v.lower from v.lower_pos)).mpr
    calc
      ((v.inverse t : ℝ) - (v.inverse s : ℝ)) * (v.lower : ℝ) =
          (v.lower : ℝ) * ((v.inverse t : ℝ) - (v.inverse s : ℝ)) := mul_comm _ _
      _ ≤ t.val - s.val := hb.1

theorem GraphPhysicalClockSpeed.inverse_tendsto (v : GraphPhysicalClockSpeed) :
    Tendsto v.inverse atTop atTop := by
  apply (tendsto_atTop_atTop_iff_of_monotone v.inverse_strictMono.monotone).mpr
  intro s
  exact ⟨v.clock s, (v.inverse_clock s).ge⟩

end TimeTraps.Analysis
