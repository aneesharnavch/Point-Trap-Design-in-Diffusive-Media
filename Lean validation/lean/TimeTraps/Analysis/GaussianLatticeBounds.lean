module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic

@[expose] public section

/-! A geometric majorant for Gaussian lattice translates, uniform on
each bounded spatial interval. All constants are derived analytically
from the positive lattice spacing and variance. -/

namespace TimeTraps.Analysis

open ProbabilityTheory Set Filter
open scoped NNReal Topology

theorem int_cast_abs_le_sq (k : ℤ) : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
  have hn : (k.natAbs : ℝ) ≤ (k.natAbs : ℝ) ^ 2 := by
    exact_mod_cast (show k.natAbs ≤ k.natAbs ^ 2 by simpa only [pow_two] using Nat.le_mul_self k.natAbs)
  simpa only [Nat.cast_natAbs, Int.cast_abs, sq_abs] using hn

theorem summable_exp_neg_int_abs {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) := by
  have hn : Summable (fun n : ℕ => Real.exp (-c * (n : ℝ))) := by
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc)
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast, Nat.abs_cast] using hn
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] using hn

noncomputable def gaussianLatticeMajorant (L x : ℝ) (v : ℝ≥0) (R : ℝ) (k : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp ((R + |x|) ^ 2 / (2 * v)) *
    Real.exp (-(L ^ 2 / v) * |(k : ℝ)|)

theorem gaussianLatticeMajorant_summable {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (R : ℝ) : Summable (gaussianLatticeMajorant L x v R) :=
  (summable_exp_neg_int_abs (div_pos (sq_pos_of_pos hL) (show (0 : ℝ) < v from hv))).mul_left _

theorem gaussianPDFReal_lattice_bound (L x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    gaussianPDFReal x v (y + k * (2 * L)) ≤ gaussianLatticeMajorant L x v R k := by
  have hvR : (0 : ℝ) < v := hv
  have hR : 0 ≤ R := (abs_nonneg y).trans hy
  have hb : |y - x| ≤ R + |x| := (abs_sub y x).trans (add_le_add hy le_rfl)
  have hb₂ : (y - x) ^ 2 ≤ (R + |x|) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (y - x)) (add_nonneg hR (abs_nonneg x))).mpr hb
  have hq : 2 * L ^ 2 * (k : ℝ) ^ 2 - (R + |x|) ^ 2 ≤
      (y + k * (2 * L) - x) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) * (2 * L) + 2 * (y - x))]
  have hk := mul_le_mul_of_nonneg_left (int_cast_abs_le_sq k)
    (show 0 ≤ 2 * L ^ 2 from mul_nonneg (by norm_num) (sq_nonneg L))
  have he : -(y + k * (2 * L) - x) ^ 2 / (2 * v) ≤
      (R + |x|) ^ 2 / (2 * v) + -(L ^ 2 / v) * |(k : ℝ)| := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hvR)).mpr
    field_simp
    nlinarith
  unfold gaussianPDFReal gaussianLatticeMajorant
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * (v : ℝ))))).trans_eq ?_
  rw [Real.exp_add]
  ring

end TimeTraps.Analysis
