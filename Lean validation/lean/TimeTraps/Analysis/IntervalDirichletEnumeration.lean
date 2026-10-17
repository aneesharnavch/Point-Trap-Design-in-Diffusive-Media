module

public import TimeTraps.Analysis.GeneralIntervalPointEnumeration
public import TimeTraps.Analysis.IntervalDirichletPositive

@[expose] public section

/-! The actual absorbing-endpoint spectrum is infinite, retains multiplicities,
and has a nondecreasing natural enumeration diverging to infinity. -/

namespace TimeTraps.Analysis

open Filter

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem DirichletPointProblem.infinite_spectralIndex (P : DirichletPointProblem ι l r) :
    Infinite (CompactSpectralIndex P.inverse) :=
  P.compactPositiveInverse.infinite_spectralIndex (intervalL2_not_finiteDimensional P.boundary.interval_pos)

noncomputable def DirichletPointProblem.spectralEnumeration (P : DirichletPointProblem ι l r) :
    ℕ ≃ CompactSpectralIndex P.inverse := by
  letI := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration

theorem DirichletPointProblem.spectralEnumeration_monotone (P : DirichletPointProblem ι l r) :
    Monotone (fun n => (P.spectralEnumeration n).1⁻¹) := by
  let := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration_monotone

theorem DirichletPointProblem.spectralEnumeration_tendsto (P : DirichletPointProblem ι l r) :
    Tendsto (fun n => (P.spectralEnumeration n).1⁻¹) atTop atTop := by
  let := P.infinite_spectralIndex
  exact P.compactPositiveInverse.spectralEnumeration_tendsto

end TimeTraps.Analysis
