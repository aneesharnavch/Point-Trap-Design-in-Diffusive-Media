module

public import TimeTraps.Analysis.PositiveTimeChangeInverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! Exact change of ordinary time under the positive integral clock.
The speed is continuous and positive; no derivative of the speed or
integrability assumption on the test is added to the change-of-variables
identity. Integrability is transported separately. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped NNReal

theorem PositiveTimeSpeed.clock_integral_substitution (v : PositiveTimeSpeed)
    (g : ℝ≥0 → ℝ) (S : ℝ≥0) :
    (∫ s in (0 : ℝ)..S.val, g (v.clock s.toNNReal) * v.rate s.toNNReal) =
      ∫ t in (0 : ℝ)..(v.clock S).val, g t.toNNReal := by
  let F : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, v.rate r.toNNReal
  have hc : Continuous (fun r : ℝ => v.rate r.toNNReal) :=
    v.continuous_rate.comp continuous_real_toNNReal
  have hd (s : ℝ) : HasDerivAt F (v.rate s.toNNReal) s :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hi := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := S.val) (g := fun t => g t.toNNReal)
    (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => hd s) (fun s _ => (v.rate_pos s.toNNReal).le)
  have hF (s : ℝ) (hs : 0 ≤ s) : (F s).toNNReal = v.clock s.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (intervalIntegral.integral_nonneg_of_forall hs
      (fun r => (v.rate_pos r.toNNReal).le)), v.clock_coe]
    exact congrArg (fun b : ℝ => ∫ r in (0 : ℝ)..b, v.rate r.toNNReal)
      (Real.coe_toNNReal s hs).symm
  have hzero : F 0 = 0 := intervalIntegral.integral_same
  have hlast : F S.val = (v.clock S).val := rfl
  rw [hzero, hlast] at hi
  calc
    _ = ∫ s in (0 : ℝ)..S.val, (fun t => g t.toNNReal) (F s) * v.rate s.toNNReal := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : (0 : ℝ) ≤ s := (le_min (le_refl 0) S.coe_nonneg).trans hs.1
      change g (v.clock s.toNNReal) * v.rate s.toNNReal =
        g ((F s).toNNReal) * v.rate s.toNNReal
      exact congrArg (fun z => g z * v.rate s.toNNReal) (hF s hs0).symm
    _ = _ := hi

theorem PositiveTimeSpeed.inverse_integral_substitution (v : PositiveTimeSpeed)
    (g : ℝ≥0 → ℝ) (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..T.val, g (v.inverse t.toNNReal)) =
      ∫ s in (0 : ℝ)..(v.inverse T).val, g s.toNNReal * v.rate s.toNNReal := by
  have hi := v.clock_integral_substitution (fun t => g (v.inverse t)) (v.inverse T)
  simpa only [v.clock_inverse, v.inverse_clock] using hi.symm

theorem PositiveTimeSpeed.inverse_integral_reciprocal (v : PositiveTimeSpeed)
    (g : ℝ≥0 → ℝ) (T : ℝ≥0) :
    (∫ s in (0 : ℝ)..(v.inverse T).val, g s.toNNReal) =
      ∫ t in (0 : ℝ)..T.val, g (v.inverse t.toNNReal) / v.rate (v.inverse t.toNNReal) := by
  have hi := v.inverse_integral_substitution (fun s => g s / v.rate s) T
  simpa only [div_mul_cancel₀ _ (v.rate_pos _).ne'] using hi.symm

end TimeTraps.Analysis
