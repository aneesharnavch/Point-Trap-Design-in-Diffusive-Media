module

public import TimeTraps.Analysis.CompactSpectralSemigroupMultiplier

@[expose] public section

/-! The actual diagonal resolvent candidate of a compact positive
injective inverse on a real Hilbert space. Nonnegative steps are allowed,
with step zero equal to the identity. Domain and inverse-graph statements
for strictly positive steps are proved in the subsequent file. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def compactResolventCoefficient {T : E →L[ℝ] E}
    (s : ℝ≥0) (i : CompactSpectralIndex T) : ℝ := i.1 / (i.1 + (s : ℝ))

theorem CompactPositiveInverse.resolventCoefficient_pos {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (i : CompactSpectralIndex T) :
    0 < compactResolventCoefficient s i :=
  div_pos (h.eigenbasis_positive i) (add_pos_of_pos_of_nonneg (h.eigenbasis_positive i) s.property)

theorem CompactPositiveInverse.resolventCoefficient_le_one {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (i : CompactSpectralIndex T) :
    compactResolventCoefficient s i ≤ 1 := by
  apply (div_le_one (add_pos_of_pos_of_nonneg (h.eigenbasis_positive i) s.property)).mpr
  exact le_add_of_nonneg_right s.property

theorem CompactPositiveInverse.resolventCoefficient_abs_le_one {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (i : CompactSpectralIndex T) :
    |compactResolventCoefficient s i| ≤ 1 := by
  rw [abs_of_pos (h.resolventCoefficient_pos s i)]
  exact h.resolventCoefficient_le_one s i

noncomputable def CompactPositiveInverse.resolvent {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) : E →L[ℝ] E :=
  hilbertContraction h.eigenbasis (compactResolventCoefficient s) (h.resolventCoefficient_abs_le_one s)

theorem CompactPositiveInverse.resolvent_inner {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) (h.resolvent s x) =
      compactResolventCoefficient s i * inner ℝ (h.eigenbasis i) x := by
  simpa only [CompactPositiveInverse.resolvent, HilbertBasis.repr_apply_apply] using
    hilbertContraction_repr h.eigenbasis (compactResolventCoefficient s)
      (h.resolventCoefficient_abs_le_one s) x i

theorem CompactPositiveInverse.resolvent_norm_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) : ‖h.resolvent s x‖ ≤ ‖x‖ :=
  hilbertContraction_norm_le h.eigenbasis (compactResolventCoefficient s)
    (h.resolventCoefficient_abs_le_one s) x

theorem CompactPositiveInverse.resolvent_opNorm_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) : ‖h.resolvent s‖ ≤ 1 :=
  hilbertContraction_opNorm_le h.eigenbasis (compactResolventCoefficient s)
    (h.resolventCoefficient_abs_le_one s)

theorem CompactPositiveInverse.resolvent_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) : h.resolvent 0 = ContinuousLinearMap.id ℝ E := by
  ext x
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, h.resolvent_inner,
    compactResolventCoefficient, NNReal.coe_zero, add_zero,
    div_self (h.eigenbasis_positive i).ne', one_mul, ContinuousLinearMap.id_apply]

theorem CompactPositiveInverse.resolvent_commutes {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) :
    T (h.resolvent s x) = h.resolvent s (T x) := by
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, h.inner_eigenbasis_apply, h.resolvent_inner]
  ring

theorem CompactPositiveInverse.hasSum_resolvent {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) :
    HasSum (fun i : CompactSpectralIndex T =>
      (compactResolventCoefficient s i * inner ℝ (h.eigenbasis i) x) • h.eigenbasis i)
      (h.resolvent s x) := by
  simpa only [h.resolvent_inner] using h.hasSum_eigenbasis (h.resolvent s x)

end TimeTraps.Analysis
