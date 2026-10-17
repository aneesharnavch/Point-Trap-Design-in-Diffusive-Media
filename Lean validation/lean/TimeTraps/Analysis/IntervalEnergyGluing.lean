module

public import TimeTraps.Analysis.IntervalEnergyLocal

@[expose] public section

/-! Gluing adjacent closed H1 intervals, including degenerate pieces. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem IntervalEnergy.trans {u : ℝ → ℝ} {a b c : ℝ}
    (hu : IntervalEnergy u a b) (hv : IntervalEnergy u b c)
    (hab : a ≤ b) (hbc : b ≤ c) : IntervalEnergy u a c := by
  have hi := hu.absolutelyContinuous.intervalIntegrable_deriv.trans
    hv.absolutelyContinuous.intervalIntegrable_deriv
  have hp (x : ℝ) (hx : x ∈ Icc a c) : (∫ t in a..x, deriv u t) = u x - u a := by
    by_cases hxb : x ≤ b
    · have he := hu.absolutelyContinuous.mono (show uIcc a x ⊆ uIcc a b by
        rw [uIcc_of_le hx.1, uIcc_of_le hab]
        exact Icc_subset_Icc le_rfl hxb)
      exact he.integral_deriv_eq_sub
    · have hbx : b ≤ x := (lt_of_not_ge hxb).le
      have he := hv.absolutelyContinuous.mono (show uIcc b x ⊆ uIcc b c by
        rw [uIcc_of_le hbx, uIcc_of_le hbc]
        exact Icc_subset_Icc le_rfl hx.2)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        hu.absolutelyContinuous.intervalIntegrable_deriv he.intervalIntegrable_deriv,
        hu.absolutelyContinuous.integral_deriv_eq_sub, he.integral_deriv_eq_sub]
      ring
  have ha := (interval_absolutelyContinuous_const (u a) a c).fun_add
    (hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  refine ⟨interval_absolutelyContinuous_congr ha ?_,
    hu.derivative_square_integrable.trans hv.derivative_square_integrable⟩
  intro x hx
  have hx' : x ∈ Icc a c := by simpa only [uIcc_of_le (hab.trans hbc)] using hx
  change u a + (∫ t in a..x, deriv u t) = u x
  rw [hp x hx']
  ring

end TimeTraps.Analysis
