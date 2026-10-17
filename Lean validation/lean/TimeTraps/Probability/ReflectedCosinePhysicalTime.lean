module

public import TimeTraps.Probability.ReflectedCosineGenerator

@[expose] public section

/-! Physical time for the actual reflected Gaussian L2 evolution. The
variance is 2*D*t, so the cosine rates are D*(n*pi/L)^2. Positive time
dilation gives an equivalence of actual strong right derivatives. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set

def reflectedCosinePhysicalRate (L D : ℝ) (n : ℕ) : ℝ :=
  D * ((n : ℝ) * Real.pi / L) ^ 2

def reflectedGaussianPhysicalL2Curve (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : ReflectedUniformL2 L hL) (t : ℝ) : ReflectedUniformL2 L hL :=
  reflectedGaussianL2Operator L hL (2 * D * t).toNNReal f

theorem reflectedCosinePhysicalRate_eq (L D : ℝ) (n : ℕ) :
    reflectedCosinePhysicalRate L D n = (2 * D) * reflectedCosineRate L n := by
  unfold reflectedCosinePhysicalRate reflectedCosineRate
  ring

theorem reflectedCosinePhysicalRate_zero (L D : ℝ) :
    reflectedCosinePhysicalRate L D 0 = 0 := by
  simp [reflectedCosinePhysicalRate]

theorem reflectedGaussianPhysicalL2Curve_coefficient (L : ℝ) (hL : 0 < L)
    {D : ℝ} (hD : 0 < D) (f : ReflectedUniformL2 L hL) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    inner ℝ (reflectedCosineHilbertBasis L hL n) (reflectedGaussianPhysicalL2Curve L hL D f t) =
      Real.exp (-t * reflectedCosinePhysicalRate L D n) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  change inner ℝ (reflectedCosineHilbertBasis L hL n)
    (reflectedGaussianL2Curve L hL f (2 * D * t)) = _
  rw [reflectedGaussianL2Curve_coefficient L hL f (by positivity), reflectedCosinePhysicalRate_eq]
  congr 2
  ring

theorem reflectedGaussianPhysicalL2Curve_derivative_iff (L : ℝ) (hL : 0 < L)
    {D : ℝ} (hD : 0 < D) (f g : ReflectedUniformL2 L hL) :
    HasDerivWithinAt (reflectedGaussianPhysicalL2Curve L hL D f) g (Ici 0) 0 ↔
      HasDerivWithinAt (reflectedGaussianL2Curve L hL f) ((2 * D)⁻¹ • g) (Ici 0) 0 := by
  change HasDerivWithinAt (fun t : ℝ => reflectedGaussianL2Curve L hL f ((2 * D) * t))
    g (Ici 0) 0 ↔ _
  have hc : 0 < 2 * D := by positivity
  constructor
  · intro hg
    have hd := hg.scomp_of_eq 0
      (((hasDerivAt_id (0 : ℝ)).const_mul (2 * D)⁻¹).hasDerivWithinAt (s := Ici 0))
      (show MapsTo (fun t : ℝ => (2 * D)⁻¹ * t) (Ici 0) (Ici 0) from
        fun t ht => mul_nonneg (inv_nonneg.mpr hc.le) ht)
      (by simp)
    simpa only [Function.comp_def, id_eq, mul_one,
      ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hd
  · intro hg
    have hd := hg.scomp_of_eq 0
      (((hasDerivAt_id (0 : ℝ)).const_mul (2 * D)).hasDerivWithinAt (s := Ici 0))
      (show MapsTo (fun t : ℝ => (2 * D) * t) (Ici 0) (Ici 0) from
        fun t ht => mul_nonneg hc.le ht)
      (by simp)
    simpa only [Function.comp_def, id_eq, mul_one,
      smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using hd

end TimeTraps.Probability

end
