module

public import TimeTraps.Probability.ReflectedCosinePhysicalTime

@[expose] public section

/-! Full generator domain and action of the actual physical-time reflected
L2 evolution T_(2Dt), for D>0. The rates are D*(n*pi/L)^2, including the
zero rate at n=0. These statements concern actual strong right derivatives;
they do not define a separate spectral evolution or assume spatial Sobolev
regularity. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set

theorem reflectedGaussianPhysicalL2Curve_generator_iff (L : ℝ) (hL : 0 < L)
    {D : ℝ} (hD : 0 < D) (f g : ReflectedUniformL2 L hL) :
    HasDerivWithinAt (reflectedGaussianPhysicalL2Curve L hL D f) g (Ici 0) 0 ↔
      ∀ n, inner ℝ (reflectedCosineHilbertBasis L hL n) g =
        -reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  rw [reflectedGaussianPhysicalL2Curve_derivative_iff L hL hD,
    reflectedGaussianL2Curve_generator_iff]
  have hc : 0 < 2 * D := by positivity
  constructor
  · intro hg n
    have hn := hg n
    rw [inner_smul_right] at hn
    rw [reflectedCosinePhysicalRate_eq]
    calc
      _ = (2 * D) * ((2 * D)⁻¹ * inner ℝ (reflectedCosineHilbertBasis L hL n) g) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
      _ = _ := by rw [hn]; ring
  · intro hg n
    rw [inner_smul_right, hg n, reflectedCosinePhysicalRate_eq]
    field_simp [hc.ne']

theorem reflectedGaussianPhysicalL2Curve_right_differentiable_iff (L : ℝ) (hL : 0 < L)
    {D : ℝ} (hD : 0 < D) (f : ReflectedUniformL2 L hL) :
    DifferentiableWithinAt ℝ (reflectedGaussianPhysicalL2Curve L hL D f) (Ici 0) 0 ↔
      Summable (fun n : ℕ =>
        (reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) := by
  have hc : 0 < 2 * D := by positivity
  have hd : DifferentiableWithinAt ℝ (reflectedGaussianPhysicalL2Curve L hL D f) (Ici 0) 0 ↔
      DifferentiableWithinAt ℝ (reflectedGaussianL2Curve L hL f) (Ici 0) 0 := by
    constructor
    · intro hf
      exact ((reflectedGaussianPhysicalL2Curve_derivative_iff L hL hD f _).mp
        hf.hasDerivWithinAt).differentiableWithinAt
    · intro hf
      apply HasDerivWithinAt.differentiableWithinAt
        (f' := (2 * D) • derivWithin (reflectedGaussianL2Curve L hL f) (Ici 0) 0)
      apply (reflectedGaussianPhysicalL2Curve_derivative_iff L hL hD f _).mpr
      simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hf.hasDerivWithinAt
  have he : (fun n : ℕ =>
      (reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) =
      (fun n : ℕ => (2 * D) ^ 2 *
        (reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) := by
    funext n
    rw [reflectedCosinePhysicalRate_eq]
    ring
  rw [hd, reflectedGaussianL2Curve_right_differentiable_iff, he,
    summable_mul_left_iff (pow_ne_zero 2 hc.ne')]

theorem reflectedGaussianPhysicalL2Curve_generator_hasSum (L : ℝ) (hL : 0 < L)
    {D : ℝ} (hD : 0 < D) {f g : ReflectedUniformL2 L hL}
    (hg : HasDerivWithinAt (reflectedGaussianPhysicalL2Curve L hL D f) g (Ici 0) 0) :
    HasSum (fun n : ℕ =>
      (-reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) •
        reflectedCosineHilbertBasis L hL n) g := by
  simpa only [HilbertBasis.repr_apply_apply,
    (reflectedGaussianPhysicalL2Curve_generator_iff L hL hD f g).mp hg] using
      (reflectedCosineHilbertBasis L hL).hasSum_repr g

theorem reflectedGaussianPhysicalL2Curve_generator_hasSum_norm (L : ℝ) (hL : 0 < L)
    {D : ℝ} (hD : 0 < D) {f g : ReflectedUniformL2 L hL}
    (hg : HasDerivWithinAt (reflectedGaussianPhysicalL2Curve L hL D f) g (Ici 0) 0) :
    HasSum (fun n : ℕ =>
      (reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2)
        (‖g‖ ^ 2) := by
  simpa only [(reflectedGaussianPhysicalL2Curve_generator_iff L hL hD f g).mp hg,
    neg_mul, neg_sq] using reflectedCosineBasis_hasSum_parseval L hL g

end TimeTraps.Probability
