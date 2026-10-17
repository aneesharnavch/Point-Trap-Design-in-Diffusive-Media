module

public import TimeTraps.Analysis.CompactSpectralReciprocal
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Set.Card

@[expose] public section

/-! Rank the reciprocal spectral values, retaining each finite eigenspace
multiplicity. The tie-breaker is the existing finite eigenspace index.
Every predecessor set is finite by compactness, so its cardinality is a
natural-number rank. -/

namespace TimeTraps.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def compactSpectralKey {T : E →L[ℝ] E} (i : CompactSpectralIndex T) : ℝ ×ₗ ℕ :=
  toLex (i.1⁻¹, i.2.val)

omit [CompleteSpace E] in
theorem compactSpectralKey_injective {T : E →L[ℝ] E} :
    Function.Injective (compactSpectralKey (T := T)) := by
  rintro ⟨μ, i⟩ ⟨ν, j⟩ hij
  have hμ : μ = ν := by
    have he := congrArg (fun p : ℝ ×ₗ ℕ => (ofLex p).1) hij
    simpa [compactSpectralKey] using he
  subst ν
  have hi : i = j := by
    apply Fin.ext
    exact congrArg (fun p : ℝ ×ₗ ℕ => (ofLex p).2) hij
  subst j
  rfl

theorem CompactPositiveInverse.finite_spectral_predecessors {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) :
    {j : CompactSpectralIndex T | compactSpectralKey j < compactSpectralKey i}.Finite := by
  apply (h.finite_reciprocals_le i.1⁻¹).subset
  intro j hj
  exact Prod.Lex.monotone_fst (compactSpectralKey j) (compactSpectralKey i) hj.le

noncomputable def compactSpectralRank {T : E →L[ℝ] E} (i : CompactSpectralIndex T) : ℕ :=
  {j : CompactSpectralIndex T | compactSpectralKey j < compactSpectralKey i}.ncard

theorem CompactPositiveInverse.spectralRank_lt {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) {i j : CompactSpectralIndex T}
    (hij : compactSpectralKey i < compactSpectralKey j) :
    compactSpectralRank i < compactSpectralRank j := by
  apply Set.ncard_lt_ncard _ (h.finite_spectral_predecessors j)
  refine ⟨fun k hk => lt_trans hk hij, ?_⟩
  intro hji
  exact lt_irrefl (compactSpectralKey i) (hji hij)

theorem CompactPositiveInverse.spectralRank_injective {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) : Function.Injective (compactSpectralRank (T := T)) := by
  intro i j hij
  apply compactSpectralKey_injective
  apply le_antisymm
  · by_contra hn
    exact (h.spectralRank_lt (lt_of_not_ge hn)).ne hij.symm
  · by_contra hn
    exact (h.spectralRank_lt (lt_of_not_ge hn)).ne hij

theorem CompactPositiveInverse.spectralRank_le_iff {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i j : CompactSpectralIndex T) :
    compactSpectralRank i ≤ compactSpectralRank j ↔ compactSpectralKey i ≤ compactSpectralKey j := by
  constructor
  · intro hr
    by_contra hn
    exact (h.spectralRank_lt (lt_of_not_ge hn)).not_ge hr
  · intro hk
    rcases hk.eq_or_lt with he | he
    · exact le_of_eq (congrArg compactSpectralRank (compactSpectralKey_injective he))
    · exact (h.spectralRank_lt he).le

end TimeTraps.Analysis
