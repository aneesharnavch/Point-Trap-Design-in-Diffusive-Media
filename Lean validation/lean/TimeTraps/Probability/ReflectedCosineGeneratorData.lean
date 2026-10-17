module

public import TimeTraps.Probability.ReflectedCosineBasis
public import TimeTraps.Probability.ReflectedGaussianL2Semigroup
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorScalar

@[expose] public section

/-! Data for the generator of the actual reflected uniform-L2 evolution.
The parameter is Gaussian variance, so its nonnegative decay rates are
(n*pi/L)^2/2 and the zero mode has rate zero. Real time is extended
constantly to negative parameters only to formulate right derivatives. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedCosineRate (L : ℝ) (n : ℕ) : ℝ := ((n : ℝ) * Real.pi / L) ^ 2 / 2

def reflectedGaussianL2Curve (L : ℝ) (hL : 0 < L) (f : ReflectedUniformL2 L hL) (t : ℝ) :
    ReflectedUniformL2 L hL := reflectedGaussianL2Operator L hL t.toNNReal f

theorem reflectedCosineRate_nonneg (L : ℝ) (n : ℕ) : 0 ≤ reflectedCosineRate L n := by
  unfold reflectedCosineRate
  positivity

theorem reflectedGaussianL2Curve_zero (L : ℝ) (hL : 0 < L) (f : ReflectedUniformL2 L hL) :
    reflectedGaussianL2Curve L hL f 0 = f := by
  simp only [reflectedGaussianL2Curve, Real.toNNReal_zero,
    reflectedGaussianL2Operator_zero, ContinuousLinearMap.id_apply]

theorem reflectedGaussianL2Curve_coefficient (L : ℝ) (hL : 0 < L)
    (f : ReflectedUniformL2 L hL) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    inner ℝ (reflectedCosineHilbertBasis L hL n) (reflectedGaussianL2Curve L hL f t) =
      Real.exp (-t * reflectedCosineRate L n) * inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  rw [reflectedGaussianL2Curve, reflectedGaussianL2Operator_cosine_coefficient,
    Real.coe_toNNReal _ ht]
  unfold reflectedCosineRate
  congr 2
  ring

theorem reflectedCosineBasis_hasSum_parseval (L : ℝ) (hL : 0 < L) (f : ReflectedUniformL2 L hL) :
    HasSum (fun n : ℕ => (inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) (‖f‖ ^ 2) := by
  simpa only [real_inner_comm f, ← pow_two, real_inner_self_eq_norm_sq] using
    (reflectedCosineHilbertBasis L hL).hasSum_inner_mul_inner f f

theorem reflectedCosineScalar_hasDerivAt (L : ℝ) (n : ℕ) :
    HasDerivAt (fun t : ℝ => Real.exp (-t * reflectedCosineRate L n))
      (-reflectedCosineRate L n) 0 := by
  simpa only [Pi.neg_apply, id_eq, neg_zero, zero_mul, Real.exp_zero, one_mul, neg_one_mul] using
    (((hasDerivAt_id (0 : ℝ)).neg.mul_const (reflectedCosineRate L n)).exp)

theorem reflectedCosineScalar_slope_error_bound (L : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |slope (fun r : ℝ => Real.exp (-r * reflectedCosineRate L n)) 0 t +
      reflectedCosineRate L n| ≤ 2 * reflectedCosineRate L n := by
  by_cases hz : reflectedCosineRate L n = 0
  · simp [hz, slope_def_field]
  · have hp : 0 < reflectedCosineRate L n := lt_of_le_of_ne (reflectedCosineRate_nonneg L n) (Ne.symm hz)
    simpa only [inv_inv, div_inv_eq_mul, neg_zero, zero_mul, Real.exp_zero, mul_one] using
      compactHeatScalar_slope_error_bound (inv_pos.mpr hp) (s := 0) le_rfl ht

end TimeTraps.Probability

end
