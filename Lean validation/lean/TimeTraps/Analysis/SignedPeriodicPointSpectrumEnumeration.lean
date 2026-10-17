module

public import TimeTraps.Analysis.SignedPeriodicPointSpectrumExpansion
public import TimeTraps.Analysis.GeneralIntervalPointEnumeration

@[expose] public section

/-! Every signed periodic finite-interval point operator has an infinite complete
spectral index, derived from the actual L2 space. Its original unshifted
eigenvalues have a nondecreasing natural enumeration tending to infinity. -/

namespace TimeTraps.Analysis

open Set Filter IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.infinite_spectralIndex (P : SignedPeriodicPointProblem ι l r) :
    Infinite (CompactSpectralIndex P.shiftedInverse) :=
  P.shiftedCompactPositiveInverse.infinite_spectralIndex
    (intervalL2_not_finiteDimensional P.boundary.interval_pos)

noncomputable def SignedPeriodicPointProblem.spectralEnumeration (P : SignedPeriodicPointProblem ι l r) :
    ℕ ≃ CompactSpectralIndex P.shiftedInverse := by
  letI := P.infinite_spectralIndex
  exact P.shiftedCompactPositiveInverse.spectralEnumeration

theorem SignedPeriodicPointProblem.spectralEnumeration_monotone (P : SignedPeriodicPointProblem ι l r) :
    Monotone (fun n => (P.spectralEnumeration n).1⁻¹ - P.massShift) := by
  let := P.infinite_spectralIndex
  exact P.shiftedCompactPositiveInverse.translated_enumeration_monotone P.massShift

theorem SignedPeriodicPointProblem.spectralEnumeration_tendsto (P : SignedPeriodicPointProblem ι l r) :
    Tendsto (fun n => (P.spectralEnumeration n).1⁻¹ - P.massShift) atTop atTop := by
  let := P.infinite_spectralIndex
  exact P.shiftedCompactPositiveInverse.translated_enumeration_tendsto P.massShift

end TimeTraps.Analysis
