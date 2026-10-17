module

public import TimeTraps.Analysis.IntervalEnergyGluing

@[expose] public section

/-! Change the cut of a periodic H1 representative by a real translation.
The pieces match at the moved cut because the original endpoint traces match. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

noncomputable def periodicShift (L r : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ L - r then u (r + x) else u (r + x - L)

theorem periodicShift_left (L r : ℝ) (u : ℝ → ℝ) {x : ℝ} (hx : x ≤ L - r) :
    periodicShift L r u x = u (r + x) := by simp only [periodicShift, if_pos hx]

theorem periodicShift_right {L r : ℝ} {u : ℝ → ℝ} (hu : u 0 = u L)
    {x : ℝ} (hx : L - r ≤ x) : periodicShift L r u x = u (r + x - L) := by
  by_cases hle : x ≤ L - r
  · have ha : r + x = L := by linarith
    rw [periodicShift_left L r u hle, ha, sub_self]
    exact hu.symm
  · simp only [periodicShift, if_neg hle]

theorem periodicShift_energy_left {L r : ℝ} {u : ℝ → ℝ}
    (hu : IntervalEnergy u 0 L) (hr : r ∈ Icc 0 L) :
    IntervalEnergy (periodicShift L r u) 0 (L - r) := by
  have he : IntervalEnergy u r L := hu.mono (by
    rw [uIcc_of_le hr.2, uIcc_of_le (hr.1.trans hr.2)]
    exact Icc_subset_Icc hr.1 le_rfl)
  have ht := he.translate hr.2 r
  rw [sub_self] at ht
  apply ht.congr
  intro x hx
  have hx' : x ∈ Icc 0 (L - r) := by simpa only [uIcc_of_le (sub_nonneg.mpr hr.2)] using hx
  exact (periodicShift_left L r u hx'.2).symm

theorem periodicShift_energy_right {L r : ℝ} {u : ℝ → ℝ}
    (hu : IntervalEnergy u 0 L) (hp : u 0 = u L) (hr : r ∈ Icc 0 L) :
    IntervalEnergy (periodicShift L r u) (L - r) L := by
  have he : IntervalEnergy u 0 r := hu.mono (by
    rw [uIcc_of_le hr.1, uIcc_of_le (hr.1.trans hr.2)]
    exact Icc_subset_Icc le_rfl hr.2)
  have ht := he.translate hr.1 (r - L)
  have ha : 0 - (r - L) = L - r := by ring
  have hb : r - (r - L) = L := by ring
  have hf : (fun x => u (r - L + x)) = (fun x => u (r + x - L)) := by
    funext x
    congr 1
    ring
  rw [ha, hb, hf] at ht
  apply ht.congr
  intro x hx
  have hx' : x ∈ Icc (L - r) L := by simpa only [uIcc_of_le (sub_le_self L hr.1)] using hx
  exact (periodicShift_right hp hx'.1).symm

theorem periodicShift_energy {L r : ℝ} {u : ℝ → ℝ}
    (hu : IntervalEnergy u 0 L) (hp : u 0 = u L) (hr : r ∈ Icc 0 L) :
    IntervalEnergy (periodicShift L r u) 0 L :=
  (periodicShift_energy_left hu hr).trans (periodicShift_energy_right hu hp hr)
    (sub_nonneg.mpr hr.2) (sub_le_self L hr.1)

theorem periodicShift_trace {L r : ℝ} {u : ℝ → ℝ} (hu : u 0 = u L) (hr : r ∈ Icc 0 L) :
    periodicShift L r u 0 = periodicShift L r u L := by
  rw [periodicShift_left L r u (sub_nonneg.mpr hr.2),
    periodicShift_right hu (sub_le_self L hr.1), add_zero, add_sub_cancel_right]

theorem periodicShift_deriv_left (L r : ℝ) (u : ℝ → ℝ) {x : ℝ} (hx : x < L - r) :
    deriv (periodicShift L r u) x = deriv u (r + x) := by
  have he : periodicShift L r u =ᶠ[𝓝 x] (fun y => u (r + y)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact periodicShift_left L r u hy.le
  rw [he.deriv_eq, deriv_comp_const_add]

theorem periodicShift_deriv_right (L r : ℝ) (u : ℝ → ℝ) {x : ℝ} (hx : L - r < x) :
    deriv (periodicShift L r u) x = deriv u (r + x - L) := by
  have he : periodicShift L r u =ᶠ[𝓝 x] (fun y => u ((r - L) + y)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    simp only [periodicShift, if_neg (not_le.mpr (show L - r < y from hy))]
    congr 1
    ring
  rw [he.deriv_eq, deriv_comp_const_add]
  congr 1
  ring

end TimeTraps.Analysis
