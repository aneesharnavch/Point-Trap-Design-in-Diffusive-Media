module

public import TimeTraps.Analysis.PeriodicShift

@[expose] public section

/-! Exact preservation of integrals by moving a periodic cut. Endpoint values
are irrelevant for integrals; they remain essential for H1 gluing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem integral_eq_of_cyclic_pieces {L r : ℝ} {f g : ℝ → ℝ}
    (hr : r ∈ Icc 0 L) (hf : IntervalIntegrable f volume 0 L)
    (hg : IntervalIntegrable g volume 0 L)
    (hleft : EqOn g (fun x => f (r + x)) (Ioo 0 (L - r)))
    (hright : EqOn g (fun x => f (r + x - L)) (Ioo (L - r) L)) :
    (∫ x in (0 : ℝ)..L, g x) = ∫ x in (0 : ℝ)..L, f x := by
  have hL : 0 ≤ L := hr.1.trans hr.2
  have hc : L - r ∈ Icc 0 L := ⟨sub_nonneg.mpr hr.2, sub_le_self L hr.1⟩
  have hgl : IntervalIntegrable g volume 0 (L - r) := hg.mono_set (by
    rw [uIcc_of_le hc.1, uIcc_of_le hL]
    exact Icc_subset_Icc le_rfl hc.2)
  have hgr : IntervalIntegrable g volume (L - r) L := hg.mono_set (by
    rw [uIcc_of_le hc.2, uIcc_of_le hL]
    exact Icc_subset_Icc hc.1 le_rfl)
  have hfl : IntervalIntegrable f volume 0 r := hf.mono_set (by
    rw [uIcc_of_le hr.1, uIcc_of_le hL]
    exact Icc_subset_Icc le_rfl hr.2)
  have hfr : IntervalIntegrable f volume r L := hf.mono_set (by
    rw [uIcc_of_le hr.2, uIcc_of_le hL]
    exact Icc_subset_Icc hr.1 le_rfl)
  have hl : (∫ x in (0 : ℝ)..(L - r), g x) = ∫ x in r..L, f x := by
    calc
      _ = ∫ x in (0 : ℝ)..(L - r), f (r + x) :=
        intervalIntegral.integral_congr_uIoo (by simpa only [uIoo_of_le hc.1] using hleft)
      _ = _ := by rw [intervalIntegral.integral_comp_add_left, add_zero, add_sub_cancel]
  have hh : (∫ x in (L - r)..L, g x) = ∫ x in (0 : ℝ)..r, f x := by
    calc
      _ = ∫ x in (L - r)..L, f (r + x - L) :=
        intervalIntegral.integral_congr_uIoo (by simpa only [uIoo_of_le hc.2] using hright)
      _ = ∫ x in (L - r)..L, f ((r - L) + x) := by
        congr 1
        funext x
        congr 1
        ring
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_left]
        have h₀ : r - L + (L - r) = 0 := by ring
        rw [h₀, sub_add_cancel]
  rw [← intervalIntegral.integral_add_adjacent_intervals hgl hgr, hl, hh, add_comm,
    intervalIntegral.integral_add_adjacent_intervals hfl hfr]

theorem periodicShift_square_integral {L r : ℝ} {u : ℝ → ℝ}
    (hu : IntervalEnergy u 0 L) (hp : u 0 = u L) (hr : r ∈ Icc 0 L) :
    (∫ x in (0 : ℝ)..L, periodicShift L r u x ^ 2) = ∫ x in (0 : ℝ)..L, u x ^ 2 := by
  apply integral_eq_of_cyclic_pieces hr hu.state_square_integrable
    (periodicShift_energy hu hp hr).state_square_integrable
  · intro x hx
    dsimp only
    rw [periodicShift_left L r u hx.2.le]
  · intro x hx
    dsimp only
    rw [periodicShift_right hp hx.1.le]

theorem periodicShift_derivative_integral {L r : ℝ} {u : ℝ → ℝ}
    (hu : IntervalEnergy u 0 L) (hp : u 0 = u L) (hr : r ∈ Icc 0 L) :
    (∫ x in (0 : ℝ)..L, deriv (periodicShift L r u) x ^ 2) =
      ∫ x in (0 : ℝ)..L, deriv u x ^ 2 := by
  apply integral_eq_of_cyclic_pieces hr hu.derivative_square_integrable
    (periodicShift_energy hu hp hr).derivative_square_integrable
  · intro x hx
    dsimp only
    rw [periodicShift_deriv_left L r u hx.2]
  · intro x hx
    dsimp only
    rw [periodicShift_deriv_right L r u hx.1]

theorem periodicShift_inverse {L r : ℝ} {u : ℝ → ℝ} (hu : u 0 = u L)
    (hr : r ∈ Icc 0 L) {x : ℝ} (hx : x ∈ Icc 0 L) :
    periodicShift L (L - r) (periodicShift L r u) x = u x := by
  have hp := periodicShift_trace hu hr
  by_cases hxr : x ≤ r
  · have hout : x ≤ L - (L - r) := by linarith
    rw [periodicShift_left L (L - r) (periodicShift L r u) hout]
    rw [periodicShift_right hu (show L - r ≤ L - r + x by linarith [hx.1])]
    congr 1
    ring
  · have hout : L - (L - r) ≤ x := by linarith
    rw [periodicShift_right hp hout]
    rw [periodicShift_left L r u (show L - r + x - L ≤ L - r by linarith [hx.2])]
    congr 1
    ring

end TimeTraps.Analysis
