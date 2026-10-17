module

public import TimeTraps.Analysis.ShiftedInverseOperator
public import TimeTraps.Analysis.CompactSpectralSemigroupSmoothingDerivative

@[expose] public section

/-! The heat family for R⁻¹-cI is exp(ct) times the heat family for R⁻¹.
It is strongly continuous and exponentially bounded; no contraction or
Markov property is asserted for arbitrary real c. -/

namespace TimeTraps.Analysis

open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def CompactPositiveInverse.translatedHeatSemigroup {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (t : ℝ≥0) : E →L[ℝ] E :=
  Real.exp (c * t) • h.heatSemigroup t

theorem CompactPositiveInverse.translatedHeatSemigroup_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) :
    h.translatedHeatSemigroup c 0 = ContinuousLinearMap.id ℝ E := by
  simp only [translatedHeatSemigroup, NNReal.coe_zero, mul_zero, Real.exp_zero, one_smul,
    h.heatSemigroup_zero]

theorem CompactPositiveInverse.translatedHeatSemigroup_add {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (s t : ℝ≥0) :
    h.translatedHeatSemigroup c (s + t) =
      (h.translatedHeatSemigroup c s).comp (h.translatedHeatSemigroup c t) := by
  ext x
  simp only [translatedHeatSemigroup, NNReal.coe_add, mul_add, Real.exp_add,
    ContinuousLinearMap.comp_apply, smul_apply, map_smul, h.heatSemigroup_add, smul_smul]
  rw [mul_comm]

theorem CompactPositiveInverse.translatedHeatSemigroup_norm_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (t : ℝ≥0) (x : E) :
    ‖h.translatedHeatSemigroup c t x‖ ≤ Real.exp (c * t) * ‖x‖ := by
  change ‖Real.exp (c * t) • h.heatSemigroup t x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (h.heatSemigroup_norm_le t x) (Real.exp_pos _).le

theorem CompactPositiveInverse.translatedHeatSemigroup_strong_continuous {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) :
    Continuous (fun t : ℝ≥0 => h.translatedHeatSemigroup c t x) :=
  (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).smul
    (h.heatSemigroup_strong_continuous x)

noncomputable def CompactPositiveInverse.translatedHeatCurve {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) (t : ℝ) : E :=
  Real.exp (c * t) • h.heatCurve x t

theorem CompactPositiveInverse.translatedHeatCurve_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) : h.translatedHeatCurve c x 0 = x := by
  simp only [translatedHeatCurve, mul_zero, Real.exp_zero, one_smul, h.heatCurve_zero]

theorem CompactPositiveInverse.translatedHeatCurve_coe {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) (t : ℝ≥0) :
    h.translatedHeatCurve c x t = h.translatedHeatSemigroup c t x := by
  simp only [translatedHeatCurve, translatedHeatSemigroup, heatCurve, Real.toNNReal_coe,
    smul_apply]

theorem CompactPositiveInverse.translatedHeatCurve_mem_domain_of_pos {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) {t : ℝ} (ht : 0 < t) :
    h.translatedHeatCurve c x t ∈ (translatedInverseOperator T h.injective c).domain :=
  (inverseOperator T h.injective).domain.smul_mem _ (h.heatCurve_mem_domain_of_pos x ht)

end TimeTraps.Analysis
