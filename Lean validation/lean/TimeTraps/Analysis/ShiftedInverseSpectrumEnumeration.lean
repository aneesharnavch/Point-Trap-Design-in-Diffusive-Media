module

public import TimeTraps.Analysis.ShiftedInverseSpectrumDomain
public import TimeTraps.Analysis.CompactSpectralEnumeration

@[expose] public section

/-! Translating the reciprocal spectrum preserves finite sublevel sets and
its natural-number ordering with multiplicities. Natural enumeration keeps
the original infinite-index hypothesis; translated eigenvalues need not be positive. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {T : E →L[ℝ] E}

theorem CompactPositiveInverse.translated_eigenvalues_tendsto_atTop
    (h : CompactPositiveInverse T) (c : ℝ) :
    Tendsto (fun i : CompactSpectralIndex T => i.1⁻¹ - c) cofinite atTop := by
  rw [tendsto_atTop]
  intro R
  filter_upwards [h.reciprocals_tendsto_atTop.eventually (eventually_ge_atTop (R + c))] with i hi
  linarith

theorem CompactPositiveInverse.finite_translated_eigenvalues_le
    (h : CompactPositiveInverse T) (c R : ℝ) :
    {i : CompactSpectralIndex T | i.1⁻¹ - c ≤ R}.Finite := by
  apply (h.finite_reciprocals_le (R + c)).subset
  intro i hi
  change i.1⁻¹ ≤ R + c
  change i.1⁻¹ - c ≤ R at hi
  linarith

theorem CompactPositiveInverse.translated_enumeration_monotone
    (h : CompactPositiveInverse T) [Infinite (CompactSpectralIndex T)] (c : ℝ) :
    Monotone (fun n => (h.spectralEnumeration n).1⁻¹ - c) := by
  intro m n hmn
  exact sub_le_sub_right (h.spectralEnumeration_monotone hmn) c

theorem CompactPositiveInverse.translated_enumeration_tendsto
    (h : CompactPositiveInverse T) [Infinite (CompactSpectralIndex T)] (c : ℝ) :
    Tendsto (fun n => (h.spectralEnumeration n).1⁻¹ - c) atTop atTop := by
  apply (h.translated_eigenvalues_tendsto_atTop c).comp
  simpa only [Nat.cofinite_eq_atTop] using h.spectralEnumeration.injective.tendsto_cofinite

end TimeTraps.Analysis
