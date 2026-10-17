module

public import TimeTraps.Probability.ReflectedCosineOrthonormal

@[expose] public section

/-! Completeness of the normalized cosine family in the original
uniform L2 space. The proof uses uniform cosine approximation of actual
continuous functions and the independently proved dense Feller embedding.
The resulting Hilbert basis diagonalizes the actual Gaussian evolution. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedL2Cosine_dense_span (L : ℝ) (hL : 0 < L) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (reflectedL2Cosine L hL))).topologicalClosure := by
  let S := (Submodule.span ℝ (Set.range (reflectedL2Cosine L hL))).topologicalClosure
  have hn (n : ℕ) : reflectedL2Cosine L hL n ∈ S :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  have hraw (n : ℕ) : reflectedFellerToL2 L hL (neumannCosine L n) ∈ S := by
    have h := S.smul_mem (reflectedCosineScale n)⁻¹ (hn n)
    simpa only [reflectedL2Cosine, smul_smul,
      inv_mul_cancel₀ (reflectedCosineScale_pos n).ne', one_smul] using h
  have hspan (f : C(Icc (0 : ℝ) L, ℝ))
      (hf : f ∈ Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n))) :
      reflectedFellerToL2 L hL f ∈ S := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨n, rfl⟩ := hf
      exact hraw n
    | zero => rw [map_zero]; exact S.zero_mem
    | add f g _ _ hf hg => rw [map_add]; exact S.add_mem hf hg
    | smul c f _ hf => rw [map_smul]; exact S.smul_mem c hf
  have hclosed : IsClosed {f : C(Icc (0 : ℝ) L, ℝ) | reflectedFellerToL2 L hL f ∈ S} :=
    (Submodule.isClosed_topologicalClosure _).preimage (reflectedFellerToL2 L hL).continuous
  have ha : (neumannCosineAlgebra L : Set C(Icc (0 : ℝ) L, ℝ)) ⊆
      {f | reflectedFellerToL2 L hL f ∈ S} := by
    intro f hf
    apply hspan f
    rw [← neumannCosineSpan_eq_natSpan]
    exact hf
  have hall (f : C(Icc (0 : ℝ) L, ℝ)) : reflectedFellerToL2 L hL f ∈ S := by
    apply closure_minimal ha hclosed
    change f ∈ (neumannCosineAlgebra L).topologicalClosure
    rw [neumannCosineAlgebra_dense L hL]
    trivial
  intro f _
  apply closure_minimal (s := Set.range (reflectedFellerToL2 L hL))
    (t := (S : Set (ReflectedUniformL2 L hL)))
    (by rintro _ ⟨g, rfl⟩; exact hall g) (Submodule.isClosed_topologicalClosure _)
  exact reflectedFellerToL2_denseRange L hL f

def reflectedCosineHilbertBasis (L : ℝ) (hL : 0 < L) :
    HilbertBasis ℕ ℝ (ReflectedUniformL2 L hL) :=
  HilbertBasis.mk (reflectedL2Cosine_orthonormal L hL) (reflectedL2Cosine_dense_span L hL)

theorem reflectedCosineHilbertBasis_apply (L : ℝ) (hL : 0 < L) (n : ℕ) :
    reflectedCosineHilbertBasis L hL n = reflectedL2Cosine L hL n := by
  exact congrFun (HilbertBasis.coe_mk (reflectedL2Cosine_orthonormal L hL)
    (reflectedL2Cosine_dense_span L hL)) n

theorem reflectedGaussianL2Operator_cosine_coefficient (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : ReflectedUniformL2 L hL) (n : ℕ) :
    inner ℝ (reflectedCosineHilbertBasis L hL n) (reflectedGaussianL2Operator L hL v f) =
      Real.exp (-(v : ℝ) * ((n : ℝ) * Real.pi / L) ^ 2 / 2) *
        inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  have hs := reflectedGaussianL2Operator_symmetric L hL v (reflectedCosineHilbertBasis L hL n) f
  change inner ℝ (reflectedGaussianL2Operator L hL v (reflectedCosineHilbertBasis L hL n)) f =
    inner ℝ (reflectedCosineHilbertBasis L hL n) (reflectedGaussianL2Operator L hL v f) at hs
  rw [← hs, reflectedCosineHilbertBasis_apply,
    reflectedGaussianL2Operator_cosine, real_inner_smul_left]

end TimeTraps.Probability

end
