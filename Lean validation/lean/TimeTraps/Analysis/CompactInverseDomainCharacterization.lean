module

public import TimeTraps.Analysis.CompactInverseDomain

@[expose] public section

/-! Exact spectral characterization of the actual inverse domain. A vector
belongs to range(T) precisely when its reciprocal-weighted eigenbasis
coefficients are square summable. The inverse norm is their square sum. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.mem_inverse_domain_iff {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    x ∈ (inverseOperator T h.injective).domain ↔
      Summable (fun i : CompactSpectralIndex T =>
        (i.1⁻¹ * inner ℝ (h.eigenbasis i) x) ^ 2) := by
  constructor
  · intro hx
    simpa only [h.inner_eigenbasis_inverse] using
      (h.hasSum_parseval (inverseOperator T h.injective ⟨x, hx⟩)).summable
  · intro hx
    have hc : Memℓp (fun i : CompactSpectralIndex T =>
        i.1⁻¹ * inner ℝ (h.eigenbasis i) x) 2 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hx
    let c : lp (fun _ : CompactSpectralIndex T => ℝ) 2 :=
      ⟨fun i => i.1⁻¹ * inner ℝ (h.eigenbasis i) x, hc⟩
    let y : E := h.eigenbasis.repr.symm c
    have hcy (i : CompactSpectralIndex T) :
        inner ℝ (h.eigenbasis i) y = i.1⁻¹ * inner ℝ (h.eigenbasis i) x := by
      rw [← HilbertBasis.repr_apply_apply]
      change h.eigenbasis.repr (h.eigenbasis.repr.symm c) i = _
      rw [LinearIsometryEquiv.apply_symm_apply]
    refine ⟨y, ?_⟩
    change T y = x
    apply h.eigenbasis.repr.injective
    apply lp.ext
    funext i
    simp only [HilbertBasis.repr_apply_apply]
    rw [h.inner_eigenbasis_apply, hcy, ← mul_assoc,
      mul_inv_cancel₀ (h.eigenbasis_positive i).ne', one_mul]

theorem CompactPositiveInverse.hasSum_inverse_norm {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain) :
    HasSum (fun i : CompactSpectralIndex T =>
      (i.1⁻¹ * inner ℝ (h.eigenbasis i) (x : E)) ^ 2)
        (‖inverseOperator T h.injective x‖ ^ 2) := by
  simpa only [h.inner_eigenbasis_inverse] using h.hasSum_parseval (inverseOperator T h.injective x)

end TimeTraps.Analysis
