module

public import TimeTraps.Spectral.CompactInverseResolventPositive
public import TimeTraps.Analysis.CompactInverseDomain

@[expose] public section

/-! The diagonal map is the actual resolvent of the unbounded inverse
operator. Positive steps send every vector into its true range domain,
solve the exact graph equation, and are the unique such solutions.
Compatibility with the original bounded inverse also proves compactness. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.resolvent_T_difference {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) :
    T (x - h.resolvent s x) = (s : ℝ) • h.resolvent s x := by
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, h.inner_eigenbasis_apply,
    inner_sub_right, h.resolvent_inner, inner_smul_right]
  change i.1 * (inner ℝ (h.eigenbasis i) x -
    (i.1 / (i.1 + (s : ℝ))) * inner ℝ (h.eigenbasis i) x) =
      (s : ℝ) * ((i.1 / (i.1 + (s : ℝ))) * inner ℝ (h.eigenbasis i) x)
  have scalar (μ a c : ℝ) (hd : μ + a ≠ 0) :
      μ * (c - (μ / (μ + a)) * c) = a * ((μ / (μ + a)) * c) := by
    field_simp [hd]
    ring
  exact scalar i.1 (s : ℝ) (inner ℝ (h.eigenbasis i) x)
    (add_pos_of_pos_of_nonneg (h.eigenbasis_positive i) s.property).ne'

theorem CompactPositiveInverse.resolvent_mem_inverse_domain {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (hs : 0 < s) (x : E) :
    h.resolvent s x ∈ (inverseOperator T h.injective).domain := by
  refine ⟨(s : ℝ)⁻¹ • (x - h.resolvent s x), ?_⟩
  change T ((s : ℝ)⁻¹ • (x - h.resolvent s x)) = _
  rw [map_smul, h.resolvent_T_difference, smul_smul,
    inv_mul_cancel₀ (show (s : ℝ) ≠ 0 from ne_of_gt hs), one_smul]

theorem CompactPositiveInverse.inverse_resolvent {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (hs : 0 < s) (x : E) :
    inverseOperator T h.injective ⟨h.resolvent s x, h.resolvent_mem_inverse_domain s hs x⟩ =
      (s : ℝ)⁻¹ • (x - h.resolvent s x) := by
  apply h.injective
  rw [inverseOperator_right_inverse, map_smul, h.resolvent_T_difference,
    smul_smul, inv_mul_cancel₀ (show (s : ℝ) ≠ 0 from ne_of_gt hs), one_smul]

theorem CompactPositiveInverse.resolvent_equation {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (hs : 0 < s) (x : E) :
    h.resolvent s x + (s : ℝ) • inverseOperator T h.injective
      ⟨h.resolvent s x, h.resolvent_mem_inverse_domain s hs x⟩ = x := by
  rw [h.inverse_resolvent s hs x, smul_smul,
    mul_inv_cancel₀ (show (s : ℝ) ≠ 0 from ne_of_gt hs), one_smul]
  abel

theorem CompactPositiveInverse.resolvent_on_range {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) :
    h.resolvent s (T x + (s : ℝ) • x) = T x := by
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, h.resolvent_inner, inner_add_right,
    inner_smul_right, h.inner_eigenbasis_apply]
  change (i.1 / (i.1 + (s : ℝ))) *
    (i.1 * inner ℝ (h.eigenbasis i) x + (s : ℝ) * inner ℝ (h.eigenbasis i) x) =
      i.1 * inner ℝ (h.eigenbasis i) x
  have scalar (μ a c : ℝ) (hd : μ + a ≠ 0) :
      (μ / (μ + a)) * (μ * c + a * c) = μ * c := by
    field_simp [hd]
  exact scalar i.1 (s : ℝ) (inner ℝ (h.eigenbasis i) x)
    (add_pos_of_pos_of_nonneg (h.eigenbasis_positive i) s.property).ne'

theorem CompactPositiveInverse.resolvent_unique {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x y z : E)
    (hg : (y, z) ∈ (inverseOperator T h.injective).graph)
    (he : y + (s : ℝ) • z = x) : y = h.resolvent s x := by
  have hz := (inverseOperator_graph_iff T h.injective y z).mp hg
  calc
    y = T z := hz.symm
    _ = h.resolvent s (T z + (s : ℝ) • z) := (h.resolvent_on_range s z).symm
    _ = h.resolvent s x := by rw [hz, he]

theorem CompactPositiveInverse.resolvent_eq_iff {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (hs : 0 < s) (x : E)
    (y : (inverseOperator T h.injective).domain) :
    h.resolvent s x = (y : E) ↔ (y : E) + (s : ℝ) • inverseOperator T h.injective y = x := by
  constructor
  · intro hy
    have he := h.resolvent_equation s hs x
    simpa only [hy] using he
  · intro he
    exact (h.resolvent_unique s x y (inverseOperator T h.injective y)
      ((inverseOperator_graph_iff T h.injective _ _).mpr
        (inverseOperator_right_inverse T h.injective y)) he).symm

theorem CompactPositiveInverse.resolvent_compact {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (hs : 0 < s) : IsCompactOperator (h.resolvent s) := by
  have he : h.resolvent s = T.comp ((s : ℝ)⁻¹ • (ContinuousLinearMap.id ℝ E - h.resolvent s)) := by
    ext x
    change h.resolvent s x = T ((s : ℝ)⁻¹ • (x - h.resolvent s x))
    rw [map_smul, h.resolvent_T_difference, smul_smul,
      inv_mul_cancel₀ (show (s : ℝ) ≠ 0 from ne_of_gt hs), one_smul]
  rw [he]
  exact h.compact.comp_clm _

end TimeTraps.Analysis
