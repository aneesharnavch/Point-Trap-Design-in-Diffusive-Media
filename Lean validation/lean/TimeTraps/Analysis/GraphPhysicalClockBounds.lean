module

public import TimeTraps.Analysis.GraphPhysicalClockData
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Positive two-sided increment bounds make the genuine Borel-speed
clock Lipschitz, strictly increasing, and onto all nonnegative time. -/

namespace TimeTraps.Analysis

open MeasureTheory Set Filter
open scoped NNReal Topology

theorem GraphPhysicalClockSpeed.clock_bounds (v : GraphPhysicalClockSpeed) (s : ℝ≥0) :
    v.lower * s ≤ v.clock s ∧ v.clock s ≤ v.upper * s := by
  have h := v.clock_increment_bounds (show (0 : ℝ≥0) ≤ s from bot_le)
  rw [v.clock_zero] at h
  change (v.lower : ℝ) * (s.val - 0) ≤ (v.clock s : ℝ) - 0 ∧
    (v.clock s : ℝ) - 0 ≤ (v.upper : ℝ) * (s.val - 0) at h
  change (v.lower : ℝ) * s.val ≤ (v.clock s : ℝ) ∧
    (v.clock s : ℝ) ≤ (v.upper : ℝ) * s.val
  simpa only [sub_zero] using h

theorem GraphPhysicalClockSpeed.clock_strictMono (v : GraphPhysicalClockSpeed) : StrictMono v.clock := by
  intro s t hst
  have h := (v.clock_increment_bounds hst.le).1
  have hp : 0 < (v.lower : ℝ) * (t.val - s.val) :=
    mul_pos (show (0 : ℝ) < v.lower from v.lower_pos) (sub_pos.mpr hst)
  change (v.clock s : ℝ) < (v.clock t : ℝ)
  linarith

theorem GraphPhysicalClockSpeed.clock_lipschitz (v : GraphPhysicalClockSpeed) :
    LipschitzWith v.upper v.clock := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  wlog hst : s ≤ t generalizing s t
  · simpa only [dist_comm] using this t s (le_of_not_ge hst)
  have hb := (v.clock_increment_bounds hst).2
  have hm := v.clock_strictMono.monotone hst
  change dist (v.clock s : ℝ) (v.clock t : ℝ) ≤ (v.upper : ℝ) * dist (s : ℝ) (t : ℝ)
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (v.clock s : ℝ) ≤ (v.clock t : ℝ) from hm)),
    abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
  simp only [neg_sub]
  convert! hb using 1

theorem GraphPhysicalClockSpeed.clock_continuous (v : GraphPhysicalClockSpeed) : Continuous v.clock :=
  v.clock_lipschitz.continuous

theorem GraphPhysicalClockSpeed.clock_unbounded (v : GraphPhysicalClockSpeed) :
    ∀ t : ℝ≥0, ∃ s : ℝ≥0, t ≤ v.clock s := by
  intro t
  refine ⟨t / v.lower, ?_⟩
  have h := (v.clock_bounds (t / v.lower)).1
  have he : v.lower * (t / v.lower) = t := by
    rw [mul_comm, div_mul_cancel₀ _ v.lower_pos.ne']
  rw [he] at h
  exact h

theorem GraphPhysicalClockSpeed.clock_tendsto (v : GraphPhysicalClockSpeed) :
    Tendsto v.clock atTop atTop :=
  (tendsto_atTop_atTop_iff_of_monotone v.clock_strictMono.monotone).mpr v.clock_unbounded

theorem GraphPhysicalClockSpeed.clock_surjective (v : GraphPhysicalClockSpeed) : Function.Surjective v.clock := by
  intro t
  obtain ⟨s, hs⟩ := v.clock_unbounded t
  have ht : t ∈ Icc (v.clock 0) (v.clock s) := by
    rw [v.clock_zero]
    exact ⟨bot_le, hs⟩
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ s from bot_le)
    v.clock_continuous.continuousOn ht
  exact ⟨r, hr⟩

end TimeTraps.Analysis
