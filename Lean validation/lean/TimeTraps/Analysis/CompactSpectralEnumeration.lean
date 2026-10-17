module

public import TimeTraps.Analysis.CompactSpectralEnumerationRank
public import Mathlib.Order.OrderIsoNat

@[expose] public section

/-! Natural-number enumeration of the reciprocal spectrum, with all
eigenspace multiplicities. Sorting is obtained from the finite spectral
predecessor ranks, rather than supplied as an assumption. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Infinite dimensionality forces the complete eigenbasis index to be infinite. -/
theorem CompactPositiveInverse.infinite_spectralIndex {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (hE : ¬FiniteDimensional ℝ E) :
    Infinite (CompactSpectralIndex T) := by
  classical
  apply not_finite_iff_infinite.mp
  intro hf
  let := hf
  let := Fintype.ofFinite (CompactSpectralIndex T)
  exact hE h.eigenbasis.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable {T : E →L[ℝ] E} (h : CompactPositiveInverse T) [Infinite (CompactSpectralIndex T)]

/-- The complete spectral index enumerated in nondecreasing reciprocal order. -/
noncomputable def CompactPositiveInverse.spectralEnumeration : ℕ ≃ CompactSpectralIndex T := by
  letI : Infinite (Set.range (compactSpectralRank (T := T))) :=
    Infinite.of_injective _ (Equiv.ofInjective _ h.spectralRank_injective).injective
  exact (Nat.Subtype.orderIsoOfNat (Set.range (compactSpectralRank (T := T)))).toEquiv.trans
    (Equiv.ofInjective _ h.spectralRank_injective).symm

theorem CompactPositiveInverse.spectralEnumeration_rank_strictMono :
    StrictMono (fun n => compactSpectralRank (h.spectralEnumeration n)) := by
  let : Infinite (Set.range (compactSpectralRank (T := T))) :=
    Infinite.of_injective _ (Equiv.ofInjective _ h.spectralRank_injective).injective
  intro m n hmn
  change compactSpectralRank ((Equiv.ofInjective _ h.spectralRank_injective).symm
    (Nat.Subtype.orderIsoOfNat (Set.range (compactSpectralRank (T := T))) m)) <
    compactSpectralRank ((Equiv.ofInjective _ h.spectralRank_injective).symm
    (Nat.Subtype.orderIsoOfNat (Set.range (compactSpectralRank (T := T))) n))
  simp only [Equiv.apply_ofInjective_symm h.spectralRank_injective]
  exact (Nat.Subtype.orderIsoOfNat (Set.range (compactSpectralRank (T := T)))).strictMono hmn

/-- Reciprocal eigenvalues form a nondecreasing sequence, allowing multiplicities. -/
theorem CompactPositiveInverse.spectralEnumeration_monotone :
    Monotone (fun n => (h.spectralEnumeration n).1⁻¹) := by
  intro m n hmn
  exact Prod.Lex.monotone_fst (compactSpectralKey (h.spectralEnumeration m))
    (compactSpectralKey (h.spectralEnumeration n))
    ((h.spectralRank_le_iff _ _).mp (h.spectralEnumeration_rank_strictMono.monotone hmn))

/-- The enumerated reciprocal eigenvalues diverge to positive infinity. -/
theorem CompactPositiveInverse.spectralEnumeration_tendsto :
    Tendsto (fun n => (h.spectralEnumeration n).1⁻¹) atTop atTop := by
  apply h.reciprocals_tendsto_atTop.comp
  simpa only [Nat.cofinite_eq_atTop] using h.spectralEnumeration.injective.tendsto_cofinite

end TimeTraps.Analysis
