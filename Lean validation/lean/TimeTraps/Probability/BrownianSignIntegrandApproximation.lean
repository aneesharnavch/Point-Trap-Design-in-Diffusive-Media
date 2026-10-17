module

public import TimeTraps.Probability.BrownianIntegralLipschitz
public import Mathlib.Data.Real.Sign
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Bounded clipped-linear approximations of sign(x-a). At x=a every
approximation is zero, matching Real.sign zero exactly. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def brownianSignApprox (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  max (-1) (min 1 (((n : ℝ) + 1) * (x - a)))

theorem brownianSignApprox_lipschitz (a : ℝ) (n : ℕ) :
    LipschitzWith ((n : ℝ≥0) + 1) (brownianSignApprox a n) := by
  have hlin : LipschitzWith ((n : ℝ≥0) + 1) (fun x : ℝ => ((n : ℝ) + 1) * (x - a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : ((n : ℝ) + 1) * (x - a) - ((n : ℝ) + 1) * (y - a) =
        ((n : ℝ) + 1) * (x - y) := by ring
    simp only [Real.dist_eq, he, abs_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), le_refl]
  exact (hlin.const_min 1).const_max (-1)

theorem brownianSignApprox_abs_le (a : ℝ) (n : ℕ) (x : ℝ) :
    |brownianSignApprox a n x| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem brownianSignApprox_at_center (a : ℝ) (n : ℕ) : brownianSignApprox a n a = 0 := by
  norm_num [brownianSignApprox]

theorem brownianSignApprox_eventually_eq (a x : ℝ) :
    ∀ᶠ n in atTop, brownianSignApprox a n x = Real.sign (x - a) := by
  rcases lt_trichotomy x a with hlt | rfl | hgt
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (a - x))
    have hpos : 0 < a - x := sub_pos.mpr hlt
    have hN' : 1 < (N : ℝ) * (a - x) := (div_lt_iff₀ hpos).mp hN
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hz : ((n : ℝ) + 1) * (x - a) ≤ -1 := by nlinarith
    rw [brownianSignApprox, Real.sign_of_neg (sub_neg.mpr hlt),
      min_eq_right (hz.trans (by norm_num)), max_eq_left hz]
  · exact Eventually.of_forall (fun n => by rw [brownianSignApprox_at_center, sub_self, Real.sign_zero])
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - a))
    have hpos : 0 < x - a := sub_pos.mpr hgt
    have hN' : 1 < (N : ℝ) * (x - a) := (div_lt_iff₀ hpos).mp hN
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hz : 1 ≤ ((n : ℝ) + 1) * (x - a) := by nlinarith
    rw [brownianSignApprox, Real.sign_of_pos hpos, min_eq_left hz, max_eq_right (by norm_num)]

theorem brownianSignApprox_tendsto (a x : ℝ) :
    Tendsto (fun n => brownianSignApprox a n x) atTop (𝓝 (Real.sign (x - a))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [brownianSignApprox_eventually_eq a x] with n hn
  exact hn.symm

theorem brownianSign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)

theorem brownianSign_abs_le (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

end TimeTraps.Probability
