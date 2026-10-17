module

public import TimeTraps.Analysis.CompactSpectralReciprocal
public import Mathlib.Analysis.Normed.Lp.lpHolder

@[expose] public section

/-! Bounded diagonal contractions on a real Hilbert space, constructed on
square-summable coefficients and transported by a complete Hilbert basis. -/

namespace TimeTraps.Analysis

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem real_diagonal_norm_le (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) (i : ι) :
    ‖a i • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
  simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs] using ha i

noncomputable def hilbertContraction (b : HilbertBasis ι ℝ E)
    (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) : E →L[ℝ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun i => a i • ContinuousLinearMap.id ℝ ℝ)
      zero_le_one (real_diagonal_norm_le a ha)).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem hilbertContraction_repr (b : HilbertBasis ι ℝ E)
    (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) (x : E) (i : ι) :
    b.repr (hilbertContraction b a ha x) i = a i * b.repr x i := by
  change b.repr (b.repr.symm _) i = _
  rw [b.repr.apply_symm_apply]
  rfl

theorem hilbertContraction_norm_le (b : HilbertBasis ι ℝ E)
    (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) (x : E) :
    ‖hilbertContraction b a ha x‖ ≤ ‖x‖ := by
  change ‖b.repr.symm _‖ ≤ ‖x‖
  rw [b.repr.symm.norm_map]
  calc
    _ ≤ 1 * ‖b.repr x‖ :=
      (lp.mapCLM 2 (fun i => a i • ContinuousLinearMap.id ℝ ℝ)
        zero_le_one (real_diagonal_norm_le a ha)).le_of_opNorm_le
        (lp.norm_mapCLM_le 2 _ zero_le_one (real_diagonal_norm_le a ha)) _
    _ = ‖x‖ := by rw [one_mul, b.repr.norm_map]

theorem hilbertContraction_opNorm_le (b : HilbertBasis ι ℝ E)
    (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) : ‖hilbertContraction b a ha‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using hilbertContraction_norm_le b a ha x

theorem hilbertContraction_one (b : HilbertBasis ι ℝ E) :
    hilbertContraction b (fun _ => 1) (fun _ => by simp) = ContinuousLinearMap.id ℝ E := by
  ext x
  apply b.repr.injective
  apply lp.ext
  funext i
  simp only [hilbertContraction_repr, one_mul, ContinuousLinearMap.id_apply]

theorem hilbertContraction_comp (b : HilbertBasis ι ℝ E)
    (a c : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) (hc : ∀ i, |c i| ≤ 1)
    (hac : ∀ i, |a i * c i| ≤ 1) :
    (hilbertContraction b a ha).comp (hilbertContraction b c hc) =
      hilbertContraction b (fun i => a i * c i) hac := by
  ext x
  apply b.repr.injective
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, hilbertContraction_repr, mul_assoc]

end TimeTraps.Analysis
