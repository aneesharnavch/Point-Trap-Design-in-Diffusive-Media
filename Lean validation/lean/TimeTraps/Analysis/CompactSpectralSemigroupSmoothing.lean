module

public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorDomain
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-! Positive-time heat evolution sends every Hilbert vector into the actual
operator domain. The reciprocal exponential bound is analytical, and the
domain conclusion follows from the complete spectral characterization. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem compactHeatScalar_reciprocal_bound {μ t : ℝ} (ht : 0 < t) :
    μ⁻¹ * Real.exp (-t / μ) ≤ 1 / t := by
  have he : (t / μ) * Real.exp (-(t / μ)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (t / μ)).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  apply (le_div_iff₀ ht).mpr
  calc
    _ = (t / μ) * Real.exp (-(t / μ)) := by rw [neg_div]; ring
    _ ≤ 1 := he

theorem CompactPositiveInverse.heat_reciprocal_square_bound {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) (x : E)
    (i : CompactSpectralIndex T) :
    (i.1⁻¹ * inner ℝ (h.eigenbasis i) (h.heatSemigroup t x)) ^ 2 ≤
      (1 / (t : ℝ)) ^ 2 * (inner ℝ (h.eigenbasis i) x) ^ 2 := by
  rw [h.heatSemigroup_inner, ← mul_assoc, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hb := compactHeatScalar_reciprocal_bound (μ := i.1) (show 0 < (t : ℝ) from ht)
  have hp : 0 ≤ i.1⁻¹ * compactHeatCoefficient t i :=
    mul_nonneg (h.reciprocal_positive i).le (compactHeatCoefficient_pos t i).le
  have ht' : 0 < (t : ℝ) := ht
  change i.1⁻¹ * compactHeatCoefficient t i ≤ 1 / (t : ℝ) at hb
  nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) ht']

theorem CompactPositiveInverse.heatSemigroup_mem_domain_of_pos {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) (x : E) :
    h.heatSemigroup t x ∈ (inverseOperator T h.injective).domain := by
  apply (h.mem_inverse_domain_iff _).mpr
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (h.heat_reciprocal_square_bound t ht x)
    ((h.hasSum_parseval x).summable.mul_left ((1 / (t : ℝ)) ^ 2))

end TimeTraps.Analysis
