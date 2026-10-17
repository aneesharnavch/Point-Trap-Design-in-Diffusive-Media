module

public import TimeTraps.Analysis.PositiveTimeChangeInverse

@[expose] public section

/-! Literal restart identities for a positive ordinary integral clock.
The restarted speed is the shifted original speed. Its clock and inverse
are derived from the integral, before any probabilistic Markov assertion. -/

namespace TimeTraps.Analysis

open MeasureTheory Set
open scoped NNReal

def PositiveTimeSpeed.restart (v : PositiveTimeSpeed) (s : ℝ≥0) : PositiveTimeSpeed where
  rate := fun t => v.rate (s + t)
  continuous_rate := v.continuous_rate.comp (continuous_const.add continuous_id)
  lower := v.lower
  upper := v.upper
  lower_pos := v.lower_pos
  lower_le := fun t => v.lower_le (s + t)
  le_upper := fun t => v.le_upper (s + t)

theorem PositiveTimeSpeed.restart_rate (v : PositiveTimeSpeed) (s t : ℝ≥0) :
    (v.restart s).rate t = v.rate (s + t) := rfl

theorem PositiveTimeSpeed.restart_clock_coe (v : PositiveTimeSpeed) (s t : ℝ≥0) :
    ((v.restart s).clock t : ℝ) = (v.clock (s + t) : ℝ) - (v.clock s : ℝ) := by
  rw [v.clock_increment]
  change (∫ r in (0 : ℝ)..t.val, v.rate (s + r.toNNReal)) =
    ∫ r in s.val..(s + t).val, v.rate r.toNNReal
  calc
    _ = ∫ r in (0 : ℝ)..t.val, v.rate (s.val + r).toNNReal := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := (uIcc_of_le t.coe_nonneg ▸ hr).1
      have he : s + r.toNNReal = (s.val + r).toNNReal := by
        apply NNReal.eq
        exact (congrArg (fun z : ℝ => s.val + z) (Real.coe_toNNReal r hr0)).trans
          (Real.coe_toNNReal (s.val + r) (add_nonneg s.coe_nonneg hr0)).symm
      exact congrArg v.rate he
    _ = _ := by
      convert! (intervalIntegral.integral_comp_add_left (fun r : ℝ => v.rate r.toNNReal) s.val
          (a := (0 : ℝ)) (b := t.val)) using 1
      rw [add_zero]
      exact congrArg (fun b : ℝ => ∫ r in s.val..b, v.rate r.toNNReal)
        (show (s + t).val = s.val + t.val from rfl)

theorem PositiveTimeSpeed.restart_clock (v : PositiveTimeSpeed) (s t : ℝ≥0) :
    v.clock (s + t) = v.clock s + (v.restart s).clock t := by
  apply NNReal.eq
  change (v.clock (s + t) : ℝ) = (v.clock s : ℝ) + ((v.restart s).clock t : ℝ)
  have h := v.restart_clock_coe s t
  linarith

theorem PositiveTimeSpeed.inverse_restart (v : PositiveTimeSpeed) (s t : ℝ≥0) :
    v.inverse (v.clock s + t) = s + (v.restart s).inverse t := by
  apply v.clock_strictMono.injective
  rw [v.clock_inverse, v.restart_clock, (v.restart s).clock_inverse]

theorem PositiveTimeSpeed.restart_inverse (v : PositiveTimeSpeed) (s t : ℝ≥0) :
    (v.restart s).inverse t = v.inverse (v.clock s + t) - s := by
  rw [v.inverse_restart, add_tsub_cancel_left]

theorem PositiveTimeSpeed.inverse_add (v : PositiveTimeSpeed) (s t : ℝ≥0) :
    v.inverse (s + t) = v.inverse s + (v.restart (v.inverse s)).inverse t := by
  simpa only [v.clock_inverse] using v.inverse_restart (v.inverse s) t

theorem PositiveTimeSpeed.timeChange_restart {α : Type*} (v : PositiveTimeSpeed)
    (Y : ℝ≥0 → α) (s t : ℝ≥0) :
    Y (v.inverse (s + t)) = Y (v.inverse s + (v.restart (v.inverse s)).inverse t) :=
  congrArg Y (v.inverse_add s t)

end TimeTraps.Analysis
