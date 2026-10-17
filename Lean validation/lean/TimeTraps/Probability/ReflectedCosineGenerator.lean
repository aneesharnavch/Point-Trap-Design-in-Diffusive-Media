module

public import TimeTraps.Probability.ReflectedCosineGeneratorDerivative
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! The complete strong right-generator domain of the actual reflected
Gaussian L2 evolution. It consists precisely of vectors whose cosine
coefficients multiplied by (n*pi/L)^2/2 are square summable. The action
is the unconditional cosine series with the negative of these coefficients.
This is a variance-parameter statement and does not assert a spatial H2
characterization. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem reflectedGaussianL2Curve_right_derivative_coeff (L : ℝ) (hL : 0 < L)
    {f g : ReflectedUniformL2 L hL}
    (hg : HasDerivWithinAt (reflectedGaussianL2Curve L hL f) g (Ici 0) 0) (n : ℕ) :
    inner ℝ (reflectedCosineHilbertBasis L hL n) g =
      -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  have hc : HasDerivWithinAt
      (fun t => inner ℝ (reflectedCosineHilbertBasis L hL n) (reflectedGaussianL2Curve L hL f t))
      (inner ℝ (reflectedCosineHilbertBasis L hL n) g) (Ici 0) 0 := by
    simpa only [Function.comp_def, innerSL_apply_apply] using
      (innerSL ℝ (reflectedCosineHilbertBasis L hL n)).hasFDerivAt.comp_hasDerivWithinAt 0 hg
  have hd : HasDerivWithinAt
      (fun t : ℝ => Real.exp (-t * reflectedCosineRate L n) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) f)
      (-reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) (Ici 0) 0 :=
    ((reflectedCosineScalar_hasDerivAt L n).mul_const
      (inner ℝ (reflectedCosineHilbertBasis L hL n) f)).hasDerivWithinAt
  have hd' := hd.congr_of_mem (fun t ht => reflectedGaussianL2Curve_coefficient L hL f ht n)
    (show (0 : ℝ) ∈ Ici 0 by simp)
  exact (hc.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hd'.derivWithin (uniqueDiffWithinAt_Ici 0))

theorem reflectedGaussianL2Curve_generator_iff (L : ℝ) (hL : 0 < L)
    (f g : ReflectedUniformL2 L hL) :
    HasDerivWithinAt (reflectedGaussianL2Curve L hL f) g (Ici 0) 0 ↔
      ∀ n, inner ℝ (reflectedCosineHilbertBasis L hL n) g =
        -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  exact ⟨fun hg n => reflectedGaussianL2Curve_right_derivative_coeff L hL hg n,
    reflectedGaussianL2Curve_hasDerivWithinAt_of_coefficients L hL⟩

theorem reflectedGaussianL2Curve_right_differentiable_iff (L : ℝ) (hL : 0 < L)
    (f : ReflectedUniformL2 L hL) :
    DifferentiableWithinAt ℝ (reflectedGaussianL2Curve L hL f) (Ici 0) 0 ↔
      Summable (fun n : ℕ =>
        (reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) := by
  constructor
  · intro hf
    have he : (fun n : ℕ =>
        (reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) =
        (fun n : ℕ => (inner ℝ (reflectedCosineHilbertBasis L hL n)
          (derivWithin (reflectedGaussianL2Curve L hL f) (Ici 0) 0)) ^ 2) := by
      funext n
      rw [reflectedGaussianL2Curve_right_derivative_coeff L hL hf.hasDerivWithinAt n]
      ring
    rw [he]
    exact (reflectedCosineBasis_hasSum_parseval L hL _).summable
  · intro hf
    have hc : Memℓp (fun n : ℕ =>
        -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) 2 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
        neg_mul, neg_sq] using hf
    let c : lp (fun _ : ℕ => ℝ) 2 :=
      ⟨fun n => -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f, hc⟩
    let g : ReflectedUniformL2 L hL := (reflectedCosineHilbertBasis L hL).repr.symm c
    have hcg (n : ℕ) : inner ℝ (reflectedCosineHilbertBasis L hL n) g =
        -reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
      rw [← HilbertBasis.repr_apply_apply]
      change (reflectedCosineHilbertBasis L hL).repr
        ((reflectedCosineHilbertBasis L hL).repr.symm c) n = _
      rw [LinearIsometryEquiv.apply_symm_apply]
    exact (reflectedGaussianL2Curve_hasDerivWithinAt_of_coefficients L hL hcg).differentiableWithinAt

theorem reflectedGaussianL2Curve_generator_hasSum (L : ℝ) (hL : 0 < L)
    {f g : ReflectedUniformL2 L hL}
    (hg : HasDerivWithinAt (reflectedGaussianL2Curve L hL f) g (Ici 0) 0) :
    HasSum (fun n : ℕ =>
      (-reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) •
        reflectedCosineHilbertBasis L hL n) g := by
  simpa only [HilbertBasis.repr_apply_apply,
    reflectedGaussianL2Curve_right_derivative_coeff L hL hg] using
      (reflectedCosineHilbertBasis L hL).hasSum_repr g

theorem reflectedGaussianL2Curve_generator_hasSum_norm (L : ℝ) (hL : 0 < L)
    {f g : ReflectedUniformL2 L hL}
    (hg : HasDerivWithinAt (reflectedGaussianL2Curve L hL f) g (Ici 0) 0) :
    HasSum (fun n : ℕ =>
      (reflectedCosineRate L n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) ^ 2) (‖g‖ ^ 2) := by
  simpa only [reflectedGaussianL2Curve_right_derivative_coeff L hL hg, neg_mul, neg_sq] using
    reflectedCosineBasis_hasSum_parseval L hL g

end TimeTraps.Probability
