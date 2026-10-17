module

public import TimeTraps.Analysis.CompactSpectralExpansion
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! Reciprocal spectral values for a positive compact inverse.  These are the
candidate eigenvalues of the corresponding unbounded operator; this file does
not construct that operator or identify its domain. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.reciprocal_positive {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) : 0 < i.1⁻¹ :=
  inv_pos.mpr (h.eigenbasis_positive i)

theorem CompactPositiveInverse.reciprocal_eigen {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) :
    i.1⁻¹ • T (h.eigenbasis i) = h.eigenbasis i := by
  rw [h.eigenbasis_eigen, smul_smul,
    inv_mul_cancel₀ (h.eigenbasis_positive i).ne', one_smul]

theorem CompactPositiveInverse.reciprocals_tendsto_atTop {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) :
    Tendsto (fun i : CompactSpectralIndex T => i.1⁻¹) cofinite atTop := by
  apply tendsto_inv_nhdsGT_zero.comp
  exact tendsto_inf.mpr ⟨h.eigenvalues_tendsto_zero,
    tendsto_principal.mpr (Eventually.of_forall h.eigenbasis_positive)⟩

theorem CompactPositiveInverse.finite_reciprocals_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (R : ℝ) :
    {i : CompactSpectralIndex T | i.1⁻¹ ≤ R}.Finite := by
  have he := h.reciprocals_tendsto_atTop.eventually (eventually_gt_atTop R)
  rw [Filter.eventually_cofinite] at he
  simpa only [not_lt] using he

theorem CompactPositiveInverse.hasSum_inverse_on_range {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    HasSum (fun i : CompactSpectralIndex T =>
      (i.1⁻¹ * inner ℝ (h.eigenbasis i) (T x)) • h.eigenbasis i) x := by
  simpa only [h.inner_eigenbasis_apply, ← mul_assoc,
    inv_mul_cancel₀ (h.eigenbasis_positive _).ne', one_mul] using h.hasSum_eigenbasis x

end TimeTraps.Analysis
