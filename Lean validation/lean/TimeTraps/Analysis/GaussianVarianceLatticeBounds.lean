module

public import TimeTraps.Analysis.GaussianLatticeSecondDerivative

@[expose] public section

/-! Lattice bounds uniform over a positive compact variance interval.
The lower variance controls denominators and the upper variance controls
the geometric decay, so differentiation in variance can be justified. -/

noncomputable section

namespace TimeTraps.Analysis

open ProbabilityTheory Set Filter
open scoped NNReal Topology

def gaussianVarianceMajorant (L x : ℝ) (a b : ℝ≥0) (R : ℝ) (k : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp ((R + |x|) ^ 2 / (2 * a)) *
    Real.exp (-(L ^ 2 / b) * |(k : ℝ)|)

def gaussianVarianceSecondMajorant (L x : ℝ) (a b : ℝ≥0) (R : ℝ) (k : ℤ) : ℝ :=
  ((R + |x| + 2 * L * |(k : ℝ)|) ^ 2 / (a : ℝ) ^ 2 + 1 / a) *
    gaussianVarianceMajorant L x a b R k

theorem gaussianLatticeMajorant_le_varianceMajorant (L x : ℝ) {a b v : ℝ≥0}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (R : ℝ) (k : ℤ) :
    gaussianLatticeMajorant L x v R k ≤ gaussianVarianceMajorant L x a b R k := by
  have haR : (0 : ℝ) < a := ha
  have havR : (a : ℝ) ≤ v := hav
  have hvbR : (v : ℝ) ≤ b := hvb
  have hvR : (0 : ℝ) < v := haR.trans_le havR
  have hpre : (Real.sqrt (2 * Real.pi * v))⁻¹ ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) haR))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left havR
        (mul_nonneg (by norm_num) Real.pi_pos.le)))
  have hexp := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left
    (sq_nonneg (R + |x|)) (mul_pos (by norm_num : (0 : ℝ) < 2) haR)
    (mul_le_mul_of_nonneg_left havR (by norm_num : (0 : ℝ) ≤ 2)))
  have hratio : L ^ 2 / (b : ℝ) ≤ L ^ 2 / v :=
    div_le_div_of_nonneg_left (sq_nonneg L) hvR hvbR
  have hdecay := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg hratio) (abs_nonneg (k : ℝ)))
  exact mul_le_mul (mul_le_mul hpre hexp (Real.exp_nonneg _)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) hdecay (Real.exp_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_nonneg _))

theorem gaussianVarianceSecondMajorant_summable {L : ℝ} (hL : 0 < L) (x : ℝ)
    (a : ℝ≥0) {b : ℝ≥0} (hb : 0 < b) (R : ℝ) :
    Summable (gaussianVarianceSecondMajorant L x a b R) := by
  let c : ℝ := L ^ 2 / b
  let C : ℝ := (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp ((R + |x|) ^ 2 / (2 * a))
  have hc : 0 < c := div_pos (sq_pos_of_pos hL) (show (0 : ℝ) < b from hb)
  have hs₁ : Summable (fun k : ℤ => |(k : ℝ)| * Real.exp (-c * |(k : ℝ)|)) := by
    simpa only [pow_one] using summable_int_abs_pow_mul_exp 1 hc
  have hs₂ := summable_int_abs_pow_mul_exp 2 hc
  have he : gaussianVarianceSecondMajorant L x a b R = fun k : ℤ =>
      (((R + |x|) ^ 2 / (a : ℝ) ^ 2 + 1 / a) * C) * Real.exp (-c * |(k : ℝ)|) +
      (4 * (R + |x|) * L / (a : ℝ) ^ 2 * C) * (|(k : ℝ)| * Real.exp (-c * |(k : ℝ)|)) +
      (4 * L ^ 2 / (a : ℝ) ^ 2 * C) * (|(k : ℝ)| ^ 2 * Real.exp (-c * |(k : ℝ)|)) := by
    funext k
    dsimp [gaussianVarianceSecondMajorant, gaussianVarianceMajorant, c, C]
    ring
  rw [he]
  exact (((summable_exp_neg_int_abs hc).mul_left _).add (hs₁.mul_left _)).add (hs₂.mul_left _)

theorem gaussianPDFSecondDerivative_variance_bound {L : ℝ} (hL : 0 < L) (x : ℝ)
    {a b v : ℝ≥0} (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b)
    {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    ‖gaussianPDFSecondDerivative x v (y + k * (2 * L))‖ ≤
      gaussianVarianceSecondMajorant L x a b R k := by
  have haR : (0 : ℝ) < a := ha
  have havR : (a : ℝ) ≤ v := hav
  have hvR : (0 : ℝ) < v := haR.trans_le havR
  have hsq : (a : ℝ) ^ 2 ≤ (v : ℝ) ^ 2 := (sq_le_sq₀ haR.le hvR.le).mpr havR
  have hc : (R + |x| + 2 * L * |(k : ℝ)|) ^ 2 / (v : ℝ) ^ 2 + 1 / v ≤
      (R + |x| + 2 * L * |(k : ℝ)|) ^ 2 / (a : ℝ) ^ 2 + 1 / a :=
    add_le_add (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos haR) hsq)
      (div_le_div_of_nonneg_left zero_le_one haR havR)
  apply (gaussianPDFSecondDerivative_lattice_bound hL x (ha.trans_le hav) hy k).trans
  exact mul_le_mul hc (gaussianLatticeMajorant_le_varianceMajorant L x ha hav hvb R k)
    (by unfold gaussianLatticeMajorant; positivity)
    (add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (div_nonneg zero_le_one haR.le))

end TimeTraps.Analysis

end
