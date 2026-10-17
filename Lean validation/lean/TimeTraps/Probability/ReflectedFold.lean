module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

/-! The triangular fold onto an interval is distance to the lattice `2L ℤ`.
The circle quotient norm provides this exact distance and its Lipschitz bound.
These deterministic results do not identify a folded process as a diffusion. -/

namespace TimeTraps.Probability

open Set

noncomputable def reflectedFold (L x : ℝ) : ℝ := ‖(x : AddCircle (2 * L))‖

theorem reflectedFold_nonneg (L x : ℝ) : 0 ≤ reflectedFold L x := norm_nonneg _

theorem reflectedFold_le (L : ℝ) (hL : 0 < L) (x : ℝ) : reflectedFold L x ≤ L := by
  have h := AddCircle.norm_le_half_period (2 * L) (x := (x : AddCircle (2 * L)))
    (by positivity)
  have heq : |2 * L| / 2 = L := by
    rw [abs_of_pos (by positivity : 0 < 2 * L)]
    ring
  exact h.trans_eq heq

theorem reflectedFold_mem (L : ℝ) (hL : 0 < L) (x : ℝ) : reflectedFold L x ∈ Icc 0 L :=
  ⟨reflectedFold_nonneg L x, reflectedFold_le L hL x⟩

theorem reflectedFold_eq_self (L : ℝ) (hL : 0 < L) (x : ℝ) (hx : x ∈ Icc 0 L) :
    reflectedFold L x = x := by
  have hnorm := (AddCircle.norm_coe_eq_abs_iff (2 * L) (x := x) (by positivity)).mpr
    (show |x| ≤ |2 * L| / 2 by
      rw [abs_of_nonneg hx.1, abs_of_pos (by positivity : 0 < 2 * L)]
      linarith [hx.2])
  exact hnorm.trans (abs_of_nonneg hx.1)

theorem reflectedFold_zero (L : ℝ) : reflectedFold L 0 = 0 := by
  simp only [reflectedFold, AddCircle.coe_zero, norm_zero]

theorem reflectedFold_periodic (L : ℝ) : Function.Periodic (reflectedFold L) (2 * L) := by
  intro x
  simp only [reflectedFold, AddCircle.coe_add_period]

theorem reflectedFold_int_period (L x : ℝ) (n : ℤ) :
    reflectedFold L (x + n * (2 * L)) = reflectedFold L x :=
  (reflectedFold_periodic L).int_mul n x

theorem reflectedFold_neg (L x : ℝ) : reflectedFold L (-x) = reflectedFold L x := by
  simp only [reflectedFold, AddCircle.coe_neg, norm_neg]

theorem reflectedFold_reflection (L x : ℝ) : reflectedFold L (2 * L - x) = reflectedFold L x := by
  rw [sub_eq_neg_add, reflectedFold_periodic, reflectedFold_neg]

theorem reflectedFold_abs_sub_le (L x y : ℝ) :
    |reflectedFold L x - reflectedFold L y| ≤ |x - y| := by
  calc
    _ ≤ ‖(x : AddCircle (2 * L)) - (y : AddCircle (2 * L))‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖x - y‖ := QuotientAddGroup.norm_mk_le_norm
    _ = _ := Real.norm_eq_abs _

theorem reflectedFold_lipschitz (L : ℝ) : LipschitzWith 1 (reflectedFold L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using reflectedFold_abs_sub_le L x y

theorem reflectedFold_continuous (L : ℝ) : Continuous (reflectedFold L) :=
  (reflectedFold_lipschitz L).continuous

theorem reflectedFold_measurable (L : ℝ) : Measurable (reflectedFold L) :=
  (reflectedFold_continuous L).measurable

end TimeTraps.Probability
