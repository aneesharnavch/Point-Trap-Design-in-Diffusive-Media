module

public import TimeTraps.Analysis.CompactSpectralSemigroupMultiplier
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-! The contraction heat semigroup of a compact positive injective inverse,
with nonnegative time and spectral coefficients `exp (-t / μ)`.  No order
preservation, Markov property, or stochastic interpretation is asserted. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def compactHeatCoefficient {T : E →L[ℝ] E}
    (t : ℝ≥0) (i : CompactSpectralIndex T) : ℝ := Real.exp (-(t : ℝ) / i.1)

omit [CompleteSpace E] in
theorem compactHeatCoefficient_pos {T : E →L[ℝ] E}
    (t : ℝ≥0) (i : CompactSpectralIndex T) : 0 < compactHeatCoefficient t i :=
  Real.exp_pos _

theorem CompactPositiveInverse.heatCoefficient_le_one {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (i : CompactSpectralIndex T) :
    compactHeatCoefficient t i ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.property)
    (h.eigenbasis_positive i).le

theorem CompactPositiveInverse.heatCoefficient_abs_le_one {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (i : CompactSpectralIndex T) :
    |compactHeatCoefficient t i| ≤ 1 := by
  rw [abs_of_pos (compactHeatCoefficient_pos t i)]
  exact h.heatCoefficient_le_one t i

omit [CompleteSpace E] in
theorem compactHeatCoefficient_zero {T : E →L[ℝ] E} (i : CompactSpectralIndex T) :
    compactHeatCoefficient 0 i = 1 := by
  simp [compactHeatCoefficient]

omit [CompleteSpace E] in
theorem compactHeatCoefficient_add {T : E →L[ℝ] E}
    (s t : ℝ≥0) (i : CompactSpectralIndex T) :
    compactHeatCoefficient (s + t) i = compactHeatCoefficient s i * compactHeatCoefficient t i := by
  simp only [compactHeatCoefficient, NNReal.coe_add, neg_add, add_div, Real.exp_add]

omit [CompleteSpace E] in
theorem compactHeatCoefficient_continuous {T : E →L[ℝ] E} (i : CompactSpectralIndex T) :
    Continuous (fun t : ℝ≥0 => compactHeatCoefficient t i) :=
  Real.continuous_exp.comp (NNReal.continuous_coe.neg.div_const i.1)

noncomputable def CompactPositiveInverse.heatSemigroup {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) : E →L[ℝ] E :=
  hilbertContraction h.eigenbasis (compactHeatCoefficient t) (h.heatCoefficient_abs_le_one t)

theorem CompactPositiveInverse.heatSemigroup_inner {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (x : E) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) (h.heatSemigroup t x) =
      compactHeatCoefficient t i * inner ℝ (h.eigenbasis i) x := by
  simpa only [CompactPositiveInverse.heatSemigroup, HilbertBasis.repr_apply_apply] using
    hilbertContraction_repr h.eigenbasis (compactHeatCoefficient t)
      (h.heatCoefficient_abs_le_one t) x i

theorem CompactPositiveInverse.heatSemigroup_norm_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (x : E) : ‖h.heatSemigroup t x‖ ≤ ‖x‖ :=
  hilbertContraction_norm_le h.eigenbasis (compactHeatCoefficient t)
    (h.heatCoefficient_abs_le_one t) x

theorem CompactPositiveInverse.heatSemigroup_opNorm_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) : ‖h.heatSemigroup t‖ ≤ 1 :=
  hilbertContraction_opNorm_le h.eigenbasis (compactHeatCoefficient t)
    (h.heatCoefficient_abs_le_one t)

theorem CompactPositiveInverse.heatSemigroup_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) : h.heatSemigroup 0 = ContinuousLinearMap.id ℝ E := by
  ext x
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, h.heatSemigroup_inner,
    compactHeatCoefficient_zero, one_mul, ContinuousLinearMap.id_apply]

theorem CompactPositiveInverse.heatSemigroup_add {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s t : ℝ≥0) :
    h.heatSemigroup (s + t) = (h.heatSemigroup s).comp (h.heatSemigroup t) := by
  ext x
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, ContinuousLinearMap.comp_apply,
    h.heatSemigroup_inner, compactHeatCoefficient_add, mul_assoc]

theorem CompactPositiveInverse.hasSum_heatSemigroup {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (x : E) :
    HasSum (fun i : CompactSpectralIndex T =>
      (compactHeatCoefficient t i * inner ℝ (h.eigenbasis i) x) • h.eigenbasis i)
      (h.heatSemigroup t x) := by
  simpa only [h.heatSemigroup_inner] using h.hasSum_eigenbasis (h.heatSemigroup t x)

end TimeTraps.Analysis
