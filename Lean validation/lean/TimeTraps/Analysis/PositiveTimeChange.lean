module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! Ordinary integral clocks for continuous time speeds with a uniform
positive lower bound and finite upper bound. All bounds concern the
actual integral; no differentiability of the speed is required. -/

namespace TimeTraps.Analysis

open MeasureTheory Set Filter
open scoped NNReal Topology

structure PositiveTimeSpeed where
  rate : ℝ≥0 → ℝ
  continuous_rate : Continuous rate
  lower : ℝ≥0
  upper : ℝ≥0
  lower_pos : 0 < lower
  lower_le : ∀ s, (lower : ℝ) ≤ rate s
  le_upper : ∀ s, rate s ≤ (upper : ℝ)

theorem PositiveTimeSpeed.rate_pos (v : PositiveTimeSpeed) (s : ℝ≥0) :
    0 < v.rate s :=
  lt_of_lt_of_le (show (0 : ℝ) < v.lower from v.lower_pos) (v.lower_le s)

noncomputable def PositiveTimeSpeed.clock (v : PositiveTimeSpeed) (s : ℝ≥0) : ℝ≥0 :=
  ⟨∫ r in (0 : ℝ)..s.val, v.rate r.toNNReal,
    intervalIntegral.integral_nonneg_of_forall s.coe_nonneg (fun r => (v.rate_pos r.toNNReal).le)⟩

theorem PositiveTimeSpeed.clock_coe (v : PositiveTimeSpeed) (s : ℝ≥0) :
    (v.clock s : ℝ) = ∫ r in (0 : ℝ)..s.val, v.rate r.toNNReal := rfl

theorem PositiveTimeSpeed.clock_zero (v : PositiveTimeSpeed) : v.clock 0 = 0 := by
  apply NNReal.eq
  exact intervalIntegral.integral_same

theorem PositiveTimeSpeed.clock_increment (v : PositiveTimeSpeed) (s t : ℝ≥0) :
    (v.clock t : ℝ) - (v.clock s : ℝ) = ∫ r in s.val..t.val, v.rate r.toNNReal := by
  have hc := v.continuous_rate.comp continuous_real_toNNReal
  exact intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable 0 t.val) (hc.intervalIntegrable 0 s.val)

theorem PositiveTimeSpeed.clock_increment_bounds (v : PositiveTimeSpeed)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (v.lower : ℝ) * (t.val - s.val) ≤ (v.clock t : ℝ) - (v.clock s : ℝ) ∧
      (v.clock t : ℝ) - (v.clock s : ℝ) ≤ (v.upper : ℝ) * (t.val - s.val) := by
  have hc := v.continuous_rate.comp continuous_real_toNNReal
  rw [v.clock_increment]
  constructor
  · have h := intervalIntegral.integral_mono_on (show s.val ≤ t.val from hst)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v.lower : ℝ)) volume s.val t.val)
      (hc.intervalIntegrable s.val t.val) (fun r _ => v.lower_le r.toNNReal)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, Function.comp_apply] using h
  · have h := intervalIntegral.integral_mono_on (show s.val ≤ t.val from hst)
      (hc.intervalIntegrable s.val t.val)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v.upper : ℝ)) volume s.val t.val)
      (fun r _ => v.le_upper r.toNNReal)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, Function.comp_apply] using h

theorem PositiveTimeSpeed.clock_bounds (v : PositiveTimeSpeed) (s : ℝ≥0) :
    v.lower * s ≤ v.clock s ∧ v.clock s ≤ v.upper * s := by
  have h := v.clock_increment_bounds (show (0 : ℝ≥0) ≤ s from bot_le)
  rw [v.clock_zero] at h
  change (v.lower : ℝ) * (s.val - 0) ≤ (v.clock s : ℝ) - 0 ∧
    (v.clock s : ℝ) - 0 ≤ (v.upper : ℝ) * (s.val - 0) at h
  change (v.lower : ℝ) * s.val ≤ (v.clock s : ℝ) ∧
    (v.clock s : ℝ) ≤ (v.upper : ℝ) * s.val
  simpa only [sub_zero] using h

theorem PositiveTimeSpeed.clock_strictMono (v : PositiveTimeSpeed) : StrictMono v.clock := by
  intro s t hst
  have h := (v.clock_increment_bounds hst.le).1
  have hp : 0 < (v.lower : ℝ) * (t.val - s.val) :=
    mul_pos (show (0 : ℝ) < v.lower from v.lower_pos) (sub_pos.mpr hst)
  change (v.clock s : ℝ) < (v.clock t : ℝ)
  linarith

theorem PositiveTimeSpeed.clock_continuous (v : PositiveTimeSpeed) : Continuous v.clock := by
  have hc := v.continuous_rate.comp continuous_real_toNNReal
  exact ((intervalIntegral.differentiable_integral_of_continuous (a := (0 : ℝ)) hc).continuous.comp
    NNReal.continuous_coe).subtype_mk _

theorem PositiveTimeSpeed.clock_unbounded (v : PositiveTimeSpeed) :
    ∀ t : ℝ≥0, ∃ s : ℝ≥0, t ≤ v.clock s := by
  intro t
  refine ⟨t / v.lower, ?_⟩
  have h := (v.clock_bounds (t / v.lower)).1
  have he : v.lower * (t / v.lower) = t := by
    rw [mul_comm, div_mul_cancel₀ _ v.lower_pos.ne']
  rw [he] at h
  exact h

theorem PositiveTimeSpeed.clock_tendsto (v : PositiveTimeSpeed) :
    Tendsto v.clock atTop atTop :=
  (tendsto_atTop_atTop_iff_of_monotone v.clock_strictMono.monotone).mpr v.clock_unbounded

theorem PositiveTimeSpeed.clock_surjective (v : PositiveTimeSpeed) : Function.Surjective v.clock := by
  intro t
  obtain ⟨s, hs⟩ := v.clock_unbounded t
  have ht : t ∈ Icc (v.clock 0) (v.clock s) := by
    rw [v.clock_zero]
    exact ⟨bot_le, hs⟩
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ s from bot_le)
    v.clock_continuous.continuousOn ht
  exact ⟨r, hr⟩

end TimeTraps.Analysis
