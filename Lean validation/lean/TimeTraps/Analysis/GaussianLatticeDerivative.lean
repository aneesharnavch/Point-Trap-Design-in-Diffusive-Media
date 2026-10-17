module

public import TimeTraps.Analysis.GaussianLatticeBounds
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Explicit Gaussian derivatives and a uniform summable derivative
majorant for lattice translates. Polynomial factors are absorbed by a
geometric exponential series; convergence is derived, not assumed. -/

noncomputable section

namespace TimeTraps.Analysis

open ProbabilityTheory Set Filter
open scoped NNReal Topology

theorem summable_int_abs_pow_mul_exp (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ => |(k : ℝ)| ^ n * Real.exp (-c * |(k : ℝ)|)) := by
  have hn := Real.summable_pow_mul_exp_neg_nat_mul n hc
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast, Nat.abs_cast] using hn
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] using hn

def gaussianPDFDerivative (x : ℝ) (v : ℝ≥0) (z : ℝ) : ℝ :=
  -(z - x) / v * gaussianPDFReal x v z

theorem gaussianPDFReal_hasDerivAt (x : ℝ) {v : ℝ≥0} (hv : 0 < v) (z : ℝ) :
    HasDerivAt (gaussianPDFReal x v) (gaussianPDFDerivative x v z) z := by
  have h := (((((hasDerivAt_id z).sub_const x).pow 2).neg).div_const (2 * (v : ℝ))).exp.const_mul
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  apply h.congr_deriv
  unfold gaussianPDFDerivative gaussianPDFReal
  dsimp
  field_simp [ne_of_gt (show (0 : ℝ) < v from hv)]

def gaussianLatticeDerivativeMajorant (L x : ℝ) (v : ℝ≥0) (R : ℝ) (k : ℤ) : ℝ :=
  (R + |x| + 2 * L * |(k : ℝ)|) / v * gaussianLatticeMajorant L x v R k

theorem gaussianLatticeDerivativeMajorant_summable {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (R : ℝ) : Summable (gaussianLatticeDerivativeMajorant L x v R) := by
  let c : ℝ := L ^ 2 / v
  let C : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp ((R + |x|) ^ 2 / (2 * v))
  have hc : 0 < c := div_pos (sq_pos_of_pos hL) (show (0 : ℝ) < v from hv)
  have hs : Summable (fun k : ℤ => |(k : ℝ)| * Real.exp (-c * |(k : ℝ)|)) := by
    simpa only [pow_one] using summable_int_abs_pow_mul_exp 1 hc
  have he : gaussianLatticeDerivativeMajorant L x v R = fun k : ℤ =>
      ((R + |x|) / v * C) * Real.exp (-c * |(k : ℝ)|) +
        (2 * L / v * C) * (|(k : ℝ)| * Real.exp (-c * |(k : ℝ)|)) := by
    funext k
    dsimp [gaussianLatticeDerivativeMajorant, gaussianLatticeMajorant, c, C]
    ring
  rw [he]
  exact ((summable_exp_neg_int_abs hc).mul_left ((R + |x|) / v * C)).add
    (hs.mul_left (2 * L / v * C))

theorem gaussianPDFDerivative_lattice_bound {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    ‖gaussianPDFDerivative x v (y + k * (2 * L))‖ ≤
      gaussianLatticeDerivativeMajorant L x v R k := by
  have hvR : (0 : ℝ) < v := hv
  have hR : 0 ≤ R := (abs_nonneg y).trans hy
  have hz : |y + (k : ℝ) * (2 * L) - x| ≤ R + |x| + 2 * L * |(k : ℝ)| := by
    calc
      _ = |(y - x) + (k : ℝ) * (2 * L)| := by congr 1; ring
      _ ≤ |y - x| + |(k : ℝ) * (2 * L)| := abs_add_le _ _
      _ ≤ (R + |x|) + |(k : ℝ) * (2 * L)| :=
        add_le_add ((abs_sub y x).trans (add_le_add hy le_rfl)) le_rfl
      _ = _ := by rw [abs_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hL)]; ring
  unfold gaussianPDFDerivative
  rw [norm_mul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hvR,
    Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  exact mul_le_mul (div_le_div_of_nonneg_right hz hvR.le)
    (gaussianPDFReal_lattice_bound L x hv hy k) (gaussianPDFReal_nonneg _ _ _)
    (div_nonneg (add_nonneg (add_nonneg hR (abs_nonneg x))
      (mul_nonneg (mul_nonneg (by norm_num) hL.le) (abs_nonneg _))) hvR.le)

end TimeTraps.Analysis

end
