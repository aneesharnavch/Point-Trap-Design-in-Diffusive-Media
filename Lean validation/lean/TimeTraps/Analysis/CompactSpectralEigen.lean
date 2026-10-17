module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-! Abstract hypotheses for a compact positive injective solution operator
on a real Hilbert space. Positivity means nonnegative quadratic form;
injectivity separately excludes a zero eigenvalue. -/

namespace TimeTraps.Analysis

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure CompactPositiveInverse (T : E →L[ℝ] E) : Prop where
  compact : IsCompactOperator T
  symmetric : T.IsSymmetric
  nonneg : ∀ x : E, 0 ≤ inner ℝ x (T x)
  injective : Function.Injective T

theorem CompactPositiveInverse.eigenspace_zero {T : E →L[ℝ] E} (h : CompactPositiveInverse T) :
    Module.End.eigenspace T.toLinearMap 0 = ⊥ := by
  rw [Module.End.eigenspace_zero]
  exact LinearMap.ker_eq_bot.mpr h.injective

theorem CompactPositiveInverse.finite_eigenspace [CompleteSpace E] {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (μ : ℝ) :
    FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ) := by
  by_cases hμ : μ = 0
  · rw [hμ, h.eigenspace_zero]
    infer_instance
  · exact T.finite_dimensional_eigenspace h.compact μ hμ

theorem CompactPositiveInverse.eigenvalue_pos {T : E →L[ℝ] E} (h : CompactPositiveInverse T)
    {μ : ℝ} {v : E} (hv : v ≠ 0) (he : T v = μ • v) : 0 < μ := by
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have heq : inner ℝ v (T v) = μ * ‖v‖ ^ 2 := by
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq]
  have hμ : 0 ≤ μ := by
    have hpos := h.nonneg v
    rw [heq] at hpos
    nlinarith
  have hne : μ ≠ 0 := by
    intro hz
    apply hv
    apply h.injective
    rw [he, hz, zero_smul, map_zero]
  exact lt_of_le_of_ne hμ hne.symm

theorem CompactPositiveInverse.eigenspaces_total [CompleteSpace E] {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) :
    (⨆ μ : ℝ, Module.End.eigenspace T.toLinearMap μ)ᗮ = ⊥ :=
  T.orthogonalComplement_iSup_eigenspaces_eq_bot h.compact h.symmetric

end TimeTraps.Analysis
