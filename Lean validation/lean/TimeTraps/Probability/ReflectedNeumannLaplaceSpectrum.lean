module

public import TimeTraps.Probability.ReflectedNeumannLaplace

@[expose] public section

/-! The actual Laplace integral has coefficients 1/(alpha+D*(n*pi/L)^2),
including the constant mode 1/alpha. Hence it lies in the genuine Neumann
generator domain and solves the actual operator resolvent equation. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

theorem reflectedNeumannLaplace_coefficient (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α) (f : ReflectedUniformL2 L hL) (n : ℕ) :
    inner ℝ (reflectedCosineHilbertBasis L hL n) (reflectedNeumannLaplace L hL D α f) =
      inner ℝ (reflectedCosineHilbertBasis L hL n) f / (α + reflectedCosinePhysicalRate L D n) := by
  have hr : 0 ≤ reflectedCosinePhysicalRate L D n := by
    unfold reflectedCosinePhysicalRate
    positivity
  calc
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) (reflectedGaussianPhysicalL2Curve L hL D f t) := by
      simpa only [reflectedNeumannLaplace, innerSL_apply_apply, inner_smul_right] using
        ((innerSL ℝ (reflectedCosineHilbertBasis L hL n)).integral_comp_comm
          (reflectedNeumannLaplace_integrable L hL D hα f)).symm
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (-(α + reflectedCosinePhysicalRate L D n) * t) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [reflectedGaussianPhysicalL2Curve_coefficient L hL hD f ht.le n, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = _ := by
      rw [integral_mul_const, reflectedLaplace_exponential_integral (add_pos_of_pos_of_nonneg hα hr),
        div_eq_mul_inv, mul_comm]

theorem reflectedNeumannLaplace_generator (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α) (f : ReflectedUniformL2 L hL) :
    HasDerivWithinAt
      (reflectedGaussianPhysicalL2Curve L hL D (reflectedNeumannLaplace L hL D α f))
      (α • reflectedNeumannLaplace L hL D α f - f) (Ici 0) 0 := by
  apply (reflectedGaussianPhysicalL2Curve_generator_iff L hL hD _ _).mpr
  intro n
  have hr : 0 ≤ reflectedCosinePhysicalRate L D n := by
    unfold reflectedCosinePhysicalRate
    positivity
  have hd : α + reflectedCosinePhysicalRate L D n ≠ 0 :=
    (add_pos_of_pos_of_nonneg hα hr).ne'
  rw [inner_sub_right, inner_smul_right, reflectedNeumannLaplace_coefficient L hL D hD hα]
  field_simp [hd]
  ring

theorem reflectedNeumannLaplace_operator_graph (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α) (f : ReflectedUniformL2 L hL) :
    (reflectedUniformL2Equiv L hL (reflectedNeumannLaplace L hL D α f),
      reflectedUniformL2Equiv L hL (f - α • reflectedNeumannLaplace L hL D α f)) ∈
        (reflectedNeumannProblem L hL D hD).operator.graph := by
  simpa only [map_sub, map_smul, neg_sub] using
    reflectedPhysical_generator_mem_neumann_graph L hL D hD
      (reflectedNeumannLaplace_generator L hL D hD hα f)

end TimeTraps.Probability
