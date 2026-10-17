module

public import TimeTraps.Analysis.GaussianLatticeDerivative

@[expose] public section

/-! The explicit second spatial Gaussian derivative and a uniform
quadratic-times-geometric majorant for its lattice translates. -/

noncomputable section

namespace TimeTraps.Analysis

open ProbabilityTheory Set Filter
open scoped NNReal Topology

def gaussianPDFSecondDerivative (x : ℝ) (v : ℝ≥0) (z : ℝ) : ℝ :=
  ((z - x) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal x v z

theorem gaussianPDFDerivative_hasDerivAt (x : ℝ) {v : ℝ≥0} (hv : 0 < v) (z : ℝ) :
    HasDerivAt (gaussianPDFDerivative x v) (gaussianPDFSecondDerivative x v z) z := by
  have h := ((((hasDerivAt_id z).sub_const x).neg).div_const (v : ℝ)).mul
    (gaussianPDFReal_hasDerivAt x hv z)
  apply h.congr_deriv
  unfold gaussianPDFDerivative gaussianPDFSecondDerivative
  dsimp
  field_simp [ne_of_gt (show (0 : ℝ) < v from hv)]
  ring

def gaussianLatticeSecondMajorant (L x : ℝ) (v : ℝ≥0) (R : ℝ) (k : ℤ) : ℝ :=
  ((R + |x| + 2 * L * |(k : ℝ)|) ^ 2 / (v : ℝ) ^ 2 + 1 / v) *
    gaussianLatticeMajorant L x v R k

theorem gaussianLatticeSecondMajorant_summable {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (R : ℝ) : Summable (gaussianLatticeSecondMajorant L x v R) := by
  let c : ℝ := L ^ 2 / v
  let C : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp ((R + |x|) ^ 2 / (2 * v))
  have hc : 0 < c := div_pos (sq_pos_of_pos hL) (show (0 : ℝ) < v from hv)
  have hs₁ : Summable (fun k : ℤ => |(k : ℝ)| * Real.exp (-c * |(k : ℝ)|)) := by
    simpa only [pow_one] using summable_int_abs_pow_mul_exp 1 hc
  have hs₂ := summable_int_abs_pow_mul_exp 2 hc
  have he : gaussianLatticeSecondMajorant L x v R = fun k : ℤ =>
      (((R + |x|) ^ 2 / (v : ℝ) ^ 2 + 1 / v) * C) * Real.exp (-c * |(k : ℝ)|) +
      (4 * (R + |x|) * L / (v : ℝ) ^ 2 * C) * (|(k : ℝ)| * Real.exp (-c * |(k : ℝ)|)) +
      (4 * L ^ 2 / (v : ℝ) ^ 2 * C) * (|(k : ℝ)| ^ 2 * Real.exp (-c * |(k : ℝ)|)) := by
    funext k
    dsimp [gaussianLatticeSecondMajorant, gaussianLatticeMajorant, c, C]
    ring
  rw [he]
  exact (((summable_exp_neg_int_abs hc).mul_left _).add (hs₁.mul_left _)).add (hs₂.mul_left _)

theorem gaussian_lattice_shift_abs_bound {L : ℝ} (hL : 0 < L) (x : ℝ)
    {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    |y + k * (2 * L) - x| ≤ R + |x| + 2 * L * |(k : ℝ)| := by
  calc
    _ = |(y - x) + (k : ℝ) * (2 * L)| := by congr 1; ring
    _ ≤ |y - x| + |(k : ℝ) * (2 * L)| := abs_add_le _ _
    _ ≤ (R + |x|) + |(k : ℝ) * (2 * L)| :=
      add_le_add ((abs_sub y x).trans (add_le_add hy le_rfl)) le_rfl
    _ = _ := by rw [abs_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hL)]; ring

theorem gaussianPDFSecondDerivative_lattice_bound {L : ℝ} (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : 0 < v) {R y : ℝ} (hy : |y| ≤ R) (k : ℤ) :
    ‖gaussianPDFSecondDerivative x v (y + k * (2 * L))‖ ≤
      gaussianLatticeSecondMajorant L x v R k := by
  have hvR : (0 : ℝ) < v := hv
  have hR : 0 ≤ R := (abs_nonneg y).trans hy
  have hM : 0 ≤ R + |x| + 2 * L * |(k : ℝ)| :=
    add_nonneg (add_nonneg hR (abs_nonneg x))
      (mul_nonneg (mul_nonneg (by norm_num) hL.le) (abs_nonneg _))
  have hz := gaussian_lattice_shift_abs_bound hL x hy k
  have hz₂ : (y + k * (2 * L) - x) ^ 2 ≤ (R + |x| + 2 * L * |(k : ℝ)|) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hz
  have hc : |(y + k * (2 * L) - x) ^ 2 / (v : ℝ) ^ 2 - 1 / v| ≤
      (R + |x| + 2 * L * |(k : ℝ)|) ^ 2 / (v : ℝ) ^ 2 + 1 / v := by
    calc
      _ ≤ |(y + k * (2 * L) - x) ^ 2 / (v : ℝ) ^ 2| + |1 / (v : ℝ)| := abs_sub _ _
      _ = (y + k * (2 * L) - x) ^ 2 / (v : ℝ) ^ 2 + 1 / v := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),
          abs_of_nonneg (div_nonneg zero_le_one hvR.le)]
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hz₂ (sq_nonneg _)) le_rfl
  unfold gaussianPDFSecondDerivative
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  exact mul_le_mul hc (gaussianPDFReal_lattice_bound L x hv hy k)
    (gaussianPDFReal_nonneg _ _ _)
    (add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (div_nonneg zero_le_one hvR.le))

end TimeTraps.Analysis

end
