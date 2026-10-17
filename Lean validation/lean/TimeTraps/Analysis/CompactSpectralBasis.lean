module

public import TimeTraps.Analysis.CompactSpectralEigen

@[expose] public section

/-! Construct a complete orthonormal eigenbasis from compactness and symmetry.
The index is a dependent sum of finite eigenspace indices, with no assumption
that the ambient Hilbert space has dimension indexed by the natural numbers. -/

namespace TimeTraps.Analysis

open Set Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def CompactSpectralIndex (T : E →L[ℝ] E) : Type :=
  (μ : ℝ) × Fin (Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ))

noncomputable def CompactPositiveInverse.finiteBasis {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (μ : ℝ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ))) ℝ
      (Module.End.eigenspace T.toLinearMap μ) := by
  let _ := h.finite_eigenspace μ
  exact stdOrthonormalBasis ℝ (Module.End.eigenspace T.toLinearMap μ)

noncomputable def CompactPositiveInverse.eigenvector {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) : E :=
  h.finiteBasis i.1 i.2

theorem CompactPositiveInverse.eigenvectors_orthonormal {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) : Orthonormal ℝ h.eigenvector := by
  constructor
  · intro i
    exact (h.finiteBasis i.1).orthonormal.1 i.2
  · rintro ⟨μ, i⟩ ⟨ν, j⟩ hij
    by_cases hμν : μ = ν
    · subst ν
      have hij' : i ≠ j := by
        intro he
        apply hij
        cases he
        rfl
      exact (h.finiteBasis μ).orthonormal.2 hij'
    · exact h.symmetric.orthogonalFamily_eigenspaces hμν (h.finiteBasis μ i) (h.finiteBasis ν j)

theorem CompactPositiveInverse.eigenspaces_le_span {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) :
    (⨆ μ : ℝ, Module.End.eigenspace T.toLinearMap μ) ≤
      Submodule.span ℝ (Set.range h.eigenvector) := by
  refine iSup_le fun μ y hy => ?_
  have he := congrArg (fun z : Module.End.eigenspace T.toLinearMap μ => (z : E))
    ((h.finiteBasis μ).sum_repr ⟨y, hy⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  rw [← he]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩

theorem CompactPositiveInverse.eigenvectors_total {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) :
    (Submodule.span ℝ (Set.range h.eigenvector))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← h.eigenspaces_total]
  exact Submodule.orthogonal_le h.eigenspaces_le_span

noncomputable def CompactPositiveInverse.eigenbasis {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) : HilbertBasis (CompactSpectralIndex T) ℝ E :=
  HilbertBasis.mkOfOrthogonalEqBot h.eigenvectors_orthonormal h.eigenvectors_total

theorem CompactPositiveInverse.eigenbasis_apply {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) :
    h.eigenbasis i = h.eigenvector i := by
  simp only [CompactPositiveInverse.eigenbasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem CompactPositiveInverse.eigenbasis_eigen {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) :
    T (h.eigenbasis i) = i.1 • h.eigenbasis i := by
  rw [h.eigenbasis_apply]
  exact Module.End.mem_eigenspace_iff.mp (h.finiteBasis i.1 i.2).property

theorem CompactPositiveInverse.eigenbasis_positive {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) : 0 < i.1 :=
  h.eigenvalue_pos (h.eigenbasis.orthonormal.ne_zero i) (h.eigenbasis_eigen i)

end TimeTraps.Analysis
