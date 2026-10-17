module

public import TimeTraps.Analysis.IntervalEnergyAbsolute
public import TimeTraps.Analysis.SignedIntervalPointVariationalMinimum

@[expose] public section

/-! An everywhere nonnegative minimizer exists in the original full-H1
physical Rayleigh class for arbitrary real contact strengths. Absolute value
preserves both terms of the actual quadratic form and the square mass.
No strict positivity or simplicity is asserted here. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.squareMass_abs (P : SignedIntervalPointProblem ι l r)
    (u : ℝ → ℝ) : P.squareMass (fun x => |u x|) = P.squareMass u :=
  interval_abs_square_mass u l r

theorem SignedIntervalPointProblem.quadraticForm_abs (P : SignedIntervalPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    P.quadraticForm (fun x => |u x|) = P.quadraticForm u :=
  hu.abs_point_form P.diffusivity P.strength P.site

theorem SignedIntervalPointProblem.nonnegative_rayleigh_minimizer
    (P : SignedIntervalPointProblem ι l r) :
    ∃ u : ℝ → ℝ, IntervalEnergy u l r ∧ (∀ x, 0 ≤ u x) ∧
      0 < P.squareMass u ∧ P.quadraticForm u / P.squareMass u = P.principalValue := by
  obtain ⟨u, hu, hm, he⟩ := P.rayleigh_minimum.1
  refine ⟨fun x => |u x|, hu.abs, fun x => abs_nonneg (u x), ?_, ?_⟩
  · rwa [P.squareMass_abs]
  · rw [P.quadraticForm_abs hu, P.squareMass_abs]
    exact he.symm

end TimeTraps.Analysis
