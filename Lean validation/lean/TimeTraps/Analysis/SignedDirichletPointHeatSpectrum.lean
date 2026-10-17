module

public import TimeTraps.Analysis.SignedDirichletPointHeatStrong
public import TimeTraps.Analysis.SignedDirichletPointVariationalMinimum

@[expose] public section

/-! The heat coefficients use the original signed eigenvalues, rather
than their coercive shifts. Parseval gives the sharp exponential bound
with the independently defined Rayleigh principal value, including
possible zero or negative values. No contraction is asserted in general. -/

namespace TimeTraps.Analysis

open InnerProductSpace
open scoped NNReal

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedDirichletPointProblem.heatSemigroup_inner
    (P : SignedDirichletPointProblem ι l r) (t : ℝ≥0) (x : IntervalSobolevL2 l r)
    (i : CompactSpectralIndex P.shiftedInverse) :
    inner ℝ (P.eigenbasis i) (P.heatSemigroup t x) =
      Real.exp (-(i.1⁻¹ - P.massShift) * (t : ℝ)) * inner ℝ (P.eigenbasis i) x := by
  change inner ℝ (P.shiftedCompactPositiveInverse.eigenbasis i)
    (Real.exp (P.massShift * t) • P.shiftedCompactPositiveInverse.heatSemigroup t x) = _
  rw [real_inner_smul_right, P.shiftedCompactPositiveInverse.heatSemigroup_inner]
  change Real.exp (P.massShift * t) * (Real.exp (-(t : ℝ) / i.1) *
    inner ℝ (P.eigenbasis i) x) = _
  rw [← mul_assoc, ← Real.exp_add]
  have hs (μ c τ : ℝ) : c * τ + -τ / μ = -(μ⁻¹ - c) * τ := by ring
  rw [hs]

theorem SignedDirichletPointProblem.hasSum_heatSemigroup
    (P : SignedDirichletPointProblem ι l r) (t : ℝ≥0) (x : IntervalSobolevL2 l r) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      (Real.exp (-(i.1⁻¹ - P.massShift) * (t : ℝ)) * inner ℝ (P.eigenbasis i) x) •
        P.eigenbasis i) (P.heatSemigroup t x) := by
  simpa only [P.heatSemigroup_inner] using P.eigenbasis_expansion (P.heatSemigroup t x)

theorem SignedDirichletPointProblem.heat_coefficient_principal_bound
    (P : SignedDirichletPointProblem ι l r) (t : ℝ≥0)
    (i : CompactSpectralIndex P.shiftedInverse) :
    Real.exp (-(i.1⁻¹ - P.massShift) * (t : ℝ)) ≤
      Real.exp (-P.principalValue * (t : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hle : P.principalValue ≤ i.1⁻¹ - P.massShift :=
    P.rayleigh_minimum.2 (P.eigenvalue_mem_rayleigh i)
  exact mul_le_mul_of_nonneg_right (neg_le_neg hle) t.property

theorem SignedDirichletPointProblem.heat_norm_sq_principal_bound
    (P : SignedDirichletPointProblem ι l r) (t : ℝ≥0) (x : IntervalSobolevL2 l r) :
    ‖P.heatSemigroup t x‖ ^ 2 ≤ Real.exp (-P.principalValue * (t : ℝ)) ^ 2 * ‖x‖ ^ 2 := by
  have hb (i : CompactSpectralIndex P.shiftedInverse) :
      (inner ℝ (P.eigenbasis i) (P.heatSemigroup t x)) ^ 2 ≤
        Real.exp (-P.principalValue * (t : ℝ)) ^ 2 * (inner ℝ (P.eigenbasis i) x) ^ 2 := by
    rw [P.heatSemigroup_inner, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have he := P.heat_coefficient_principal_bound t i
    nlinarith [Real.exp_pos (-(i.1⁻¹ - P.massShift) * (t : ℝ)),
      Real.exp_pos (-P.principalValue * (t : ℝ))]
  exact hasSum_le hb (P.eigenbasis_parseval (P.heatSemigroup t x))
    ((P.eigenbasis_parseval x).mul_left (Real.exp (-P.principalValue * (t : ℝ)) ^ 2))

theorem SignedDirichletPointProblem.heat_norm_principal_bound
    (P : SignedDirichletPointProblem ι l r) (t : ℝ≥0) (x : IntervalSobolevL2 l r) :
    ‖P.heatSemigroup t x‖ ≤ Real.exp (-P.principalValue * (t : ℝ)) * ‖x‖ := by
  have hb := P.heat_norm_sq_principal_bound t x
  have hp : 0 ≤ Real.exp (-P.principalValue * (t : ℝ)) * ‖x‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  rw [← mul_pow] at hb
  exact (sq_le_sq₀ (norm_nonneg _) hp).mp hb

theorem SignedDirichletPointProblem.heatCurve_norm_principal_bound
    (P : SignedDirichletPointProblem ι l r) (x : IntervalSobolevL2 l r)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖P.heatCurve x t‖ ≤ Real.exp (-P.principalValue * t) * ‖x‖ := by
  have he : P.heatCurve x t = P.heatSemigroup ⟨t, ht⟩ x := P.heatCurve_coe x ⟨t, ht⟩
  rw [he]
  exact P.heat_norm_principal_bound ⟨t, ht⟩ x

end TimeTraps.Analysis
