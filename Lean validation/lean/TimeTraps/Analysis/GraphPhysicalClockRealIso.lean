module

public import TimeTraps.Analysis.GraphPhysicalClockRealData

@[expose] public section

/-! The Borel-speed integral clock extends to a genuine real order
isomorphism. On nonnegative time its inverse is the original inverse clock. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphPhysicalClockSpeed.realClock_surjective (v : GraphPhysicalClockSpeed) :
    Function.Surjective v.realClock := by
  intro t
  by_cases ht : 0 ≤ t
  · refine ⟨(v.inverse t.toNNReal : ℝ), ?_⟩
    have hh := congrArg (fun r : ℝ≥0 => (r : ℝ)) (v.clock_inverse t.toNNReal)
    rw [Real.coe_toNNReal t ht] at hh
    exact hh
  · refine ⟨t / v.rate 0, ?_⟩
    rw [v.realClock_nonpositive (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) (v.rate_pos 0).le),
      div_mul_cancel₀ _ (v.rate_pos 0).ne']

noncomputable def GraphPhysicalClockSpeed.realOrderIso (v : GraphPhysicalClockSpeed) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective v.realClock v.realClock_strictMono v.realClock_surjective

theorem GraphPhysicalClockSpeed.realOrderIso_apply (v : GraphPhysicalClockSpeed) (r : ℝ) :
    v.realOrderIso r = v.realClock r := rfl

theorem GraphPhysicalClockSpeed.realOrderIso_clock (v : GraphPhysicalClockSpeed) (t : ℝ≥0) :
    v.realOrderIso (t : ℝ) = (v.clock t : ℝ) := rfl

theorem GraphPhysicalClockSpeed.realOrderIso_inverse (v : GraphPhysicalClockSpeed) (t : ℝ≥0) :
    v.realOrderIso.symm (t : ℝ) = (v.inverse t : ℝ) := by
  apply v.realOrderIso.injective
  rw [v.realOrderIso.apply_symm_apply, v.realOrderIso_clock, v.clock_inverse]

theorem GraphPhysicalClockSpeed.realOrderIso_zero (v : GraphPhysicalClockSpeed) :
    v.realOrderIso 0 = 0 := by
  change v.realClock 0 = 0
  simp only [realClock, intervalIntegral.integral_same]

end TimeTraps.Analysis
