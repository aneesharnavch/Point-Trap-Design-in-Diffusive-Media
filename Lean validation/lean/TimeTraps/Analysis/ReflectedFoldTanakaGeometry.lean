module

public import TimeTraps.Analysis.ReflectedFoldTanakaSlope
public import TimeTraps.Analysis.ReflectedFoldDensityPreimage
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

@[expose] public section

/-! The stabilized finite sign sum is the periodic slope of the fold:
+1 on rising cells, -1 on falling cells, and zero at every corner.
Both its finite approximants and its pointwise limit are measurable. -/

namespace TimeTraps.Analysis

open Set Filter MeasureTheory TimeTraps.Probability
open scoped Topology

theorem reflectedFoldSlope_eq_cutoff (L : ℝ) (hL : 0 < L) (N : ℕ) (z : ℝ)
    (hz : |z| < (N + 1 : ℕ) * L) : reflectedFoldSlope L z = reflectedFoldTanakaSlopeApprox L N z := by
  obtain ⟨M, he, hM⟩ := ((reflectedFoldTanakaSlopeApprox_eventually_eq L hL z).and
    (eventually_ge_atTop N)).exists
  rw [← he]
  exact reflectedFoldTanakaSlopeApprox_stable L hL z hM hz

theorem reflectedFoldSlope_neg (L z : ℝ) : reflectedFoldSlope L (-z) = -reflectedFoldSlope L z := by
  unfold reflectedFoldSlope
  rw [abs_neg, reflectedFoldTanakaSlopeApprox_neg]

theorem reflectedFoldSlope_nat_cell (L : ℝ) (hL : 0 < L) (N : ℕ) (z : ℝ)
    (hz : z ∈ Ioo ((N : ℝ) * L) ((N + 1 : ℕ) * L)) :
    reflectedFoldSlope L z = (-1 : ℝ) ^ N := by
  have hz0 : 0 ≤ z := le_trans (mul_nonneg (Nat.cast_nonneg N) hL.le) hz.1.le
  rw [reflectedFoldSlope_eq_cutoff L hL N z (by rw [abs_of_nonneg hz0]; exact hz.2),
    reflectedFoldTanakaSlopeApprox_tail L hL N z hz.1]

theorem reflectedFoldSlope_nat_corner (L : ℝ) (hL : 0 < L) (N : ℕ) :
    reflectedFoldSlope L (N * L) = 0 := by
  have hn : |(N : ℝ) * L| < (N + 1 : ℕ) * L := by
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) hL.le)]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self N) hL
  rw [reflectedFoldSlope_eq_cutoff L hL N _ hn]
  cases N with
  | zero => simp [reflectedFoldTanakaSlopeApprox_zero]
  | succ N => exact reflectedFoldTanakaSlopeApprox_corner L hL N

theorem reflectedFoldSlope_rising (L : ℝ) (hL : 0 < L) (k : ℤ) (r : ℝ)
    (hr : r ∈ Ioo 0 L) : reflectedFoldSlope L (r + k * (2 * L)) = 1 := by
  cases k with
  | ofNat n =>
      have hi : r + (n : ℤ) * (2 * L) ∈ Ioo ((2 * n : ℕ) * L) ((2 * n + 1 : ℕ) * L) := by
        push_cast
        constructor <;> nlinarith [hr.1, hr.2]
      exact (reflectedFoldSlope_nat_cell L hL (2 * n) _ hi).trans
        (show Even (2 * n) from ⟨n, by omega⟩).neg_one_pow
  | negSucc n =>
      have hi : -(r + (Int.negSucc n : ℝ) * (2 * L)) ∈
          Ioo ((2 * n + 1 : ℕ) * L) ((2 * n + 1 + 1 : ℕ) * L) := by
        push_cast
        constructor <;> nlinarith [hr.1, hr.2]
      have he := reflectedFoldSlope_nat_cell L hL (2 * n + 1) _ hi
      rw [reflectedFoldSlope_neg, (show Odd (2 * n + 1) from ⟨n, rfl⟩).neg_one_pow] at he
      linarith

theorem reflectedFoldSlope_falling (L : ℝ) (hL : 0 < L) (k : ℤ) (r : ℝ)
    (hr : r ∈ Ioo 0 L) : reflectedFoldSlope L (-r + k * (2 * L)) = -1 := by
  rw [show -r + (k : ℝ) * (2 * L) = -(r + (-k : ℤ) * (2 * L)) by push_cast; ring,
    reflectedFoldSlope_neg, reflectedFoldSlope_rising L hL (-k) r hr]

theorem reflectedFoldSlope_int_corner (L : ℝ) (hL : 0 < L) (j : ℤ) :
    reflectedFoldSlope L (j * L) = 0 := by
  cases j with
  | ofNat n => exact reflectedFoldSlope_nat_corner L hL n
  | negSucc n =>
      rw [show (Int.negSucc n : ℝ) * L = -((n + 1 : ℕ) * L) by push_cast; ring,
        reflectedFoldSlope_neg, reflectedFoldSlope_nat_corner L hL (n + 1), neg_zero]

theorem reflectedFoldSlope_periodic (L : ℝ) (hL : 0 < L) :
    Function.Periodic (reflectedFoldSlope L) (2 * L) := by
  intro z
  let r := reflectedFold L z
  have hr : r ∈ Icc 0 L := reflectedFold_mem L hL z
  obtain ⟨k, hk | hk⟩ := (reflectedFold_eq_iff_lattice L hL z r hr).mp rfl
  all_goals
    by_cases h0 : r = 0
    · have hz : z = (2 * k : ℤ) * L := by rw [h0] at hk; push_cast; linarith
      rw [hz, show (2 * k : ℤ) * L + 2 * L = (2 * k + 2 : ℤ) * L by push_cast; ring,
        reflectedFoldSlope_int_corner, reflectedFoldSlope_int_corner] <;> exact hL
    · by_cases h1 : r = L
      · have hz : ∃ j : ℤ, z = j * L := by
          rw [h1] at hk
          first
          | exact ⟨2 * k + 1, by push_cast; linarith⟩
          | exact ⟨2 * k - 1, by push_cast; linarith⟩
        obtain ⟨j, rfl⟩ := hz
        rw [show (j : ℝ) * L + 2 * L = (j + 2 : ℤ) * L by push_cast; ring,
          reflectedFoldSlope_int_corner, reflectedFoldSlope_int_corner] <;> exact hL
      · have hi : r ∈ Ioo 0 L := ⟨lt_of_le_of_ne hr.1 (Ne.symm h0), lt_of_le_of_ne hr.2 h1⟩
        first
        | rw [hk, show r + (k : ℝ) * (2 * L) + 2 * L = r + (k + 1 : ℤ) * (2 * L) by push_cast; ring,
            reflectedFoldSlope_rising L hL (k + 1) r hi, reflectedFoldSlope_rising L hL k r hi]
        | rw [hk, show -r + (k : ℝ) * (2 * L) + 2 * L = -r + (k + 1 : ℤ) * (2 * L) by push_cast; ring,
            reflectedFoldSlope_falling L hL (k + 1) r hi, reflectedFoldSlope_falling L hL k r hi]

theorem reflectedFoldTanakaSlopeApprox_measurable (L : ℝ) (N : ℕ) :
    Measurable (reflectedFoldTanakaSlopeApprox L N) := by
  have hs : Measurable Real.sign := by
    unfold Real.sign
    exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
      (measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)
  unfold reflectedFoldTanakaSlopeApprox
  exact hs.add (Finset.measurable_sum _ (fun j _ => measurable_const.mul
    ((hs.comp (measurable_id.sub measurable_const)).add (hs.comp (measurable_id.add measurable_const)))))

theorem reflectedFoldSlope_measurable (L : ℝ) (hL : 0 < L) : Measurable (reflectedFoldSlope L) :=
  measurable_of_tendsto_metrizable (reflectedFoldTanakaSlopeApprox_measurable L)
    (tendsto_pi_nhds.mpr (reflectedFoldTanakaSlopeApprox_tendsto L hL))

end TimeTraps.Analysis
