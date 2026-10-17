module

public import TimeTraps.Analysis.IntervalSeparatedWeighted
public import TimeTraps.Analysis.IntervalContinuousMultiplierOrder
public import TimeTraps.Analysis.IntervalPointFormSemiboundedHilbert

@[expose] public section

/-! Independent regular Sturm data: positive continuous conductance p and
speed w, a continuous real potential q, finite real delta interactions,
and any selected zero endpoints. Real Robin coefficients are represented
by endpoint contact labels at the endpoints not selected to be zero. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

structure RegularSturmProblem (ι : Type*) [Fintype ι] (l r : ℝ) where
  boundary : IntervalSeparatedBoundary l r
  conductance : ℝ → ℝ
  conductance_continuous : ContinuousOn conductance (Icc l r)
  conductance_pos : ∀ x ∈ Icc l r, 0 < conductance x
  speed : ℝ → ℝ
  speed_continuous : ContinuousOn speed (Icc l r)
  speed_pos : ∀ x ∈ Icc l r, 0 < speed x
  potential : ℝ → ℝ
  potential_continuous : ContinuousOn potential (Icc l r)
  strength : ι → ℝ
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc l r

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.conductance_lower_exists (P : RegularSturmProblem ι l r) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc l r, m ≤ P.conductance x :=
  intervalContinuousCoefficient_pos_lower P.boundary.interval_pos P.conductance
    P.conductance_continuous P.conductance_pos

theorem RegularSturmProblem.speed_lower_exists (P : RegularSturmProblem ι l r) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc l r, m ≤ P.speed x :=
  intervalContinuousCoefficient_pos_lower P.boundary.interval_pos P.speed
    P.speed_continuous P.speed_pos

noncomputable def RegularSturmProblem.conductanceLower (P : RegularSturmProblem ι l r) : ℝ :=
  P.conductance_lower_exists.choose

noncomputable def RegularSturmProblem.speedLower (P : RegularSturmProblem ι l r) : ℝ :=
  P.speed_lower_exists.choose

theorem RegularSturmProblem.conductanceLower_pos (P : RegularSturmProblem ι l r) :
    0 < P.conductanceLower := P.conductance_lower_exists.choose_spec.1

theorem RegularSturmProblem.conductanceLower_le (P : RegularSturmProblem ι l r) :
    ∀ x ∈ Icc l r, P.conductanceLower ≤ P.conductance x :=
  P.conductance_lower_exists.choose_spec.2

theorem RegularSturmProblem.speedLower_pos (P : RegularSturmProblem ι l r) :
    0 < P.speedLower := P.speed_lower_exists.choose_spec.1

theorem RegularSturmProblem.speedLower_le (P : RegularSturmProblem ι l r) :
    ∀ x ∈ Icc l r, P.speedLower ≤ P.speed x := P.speed_lower_exists.choose_spec.2

noncomputable def RegularSturmProblem.stateL (P : RegularSturmProblem ι l r) :
    IntervalSeparatedSpace P.boundary →L[ℝ] IntervalSobolevL2 l r :=
  P.boundary.weightedStateL P.speed P.speed_continuous

theorem RegularSturmProblem.stateL_injective (P : RegularSturmProblem ι l r) :
    Function.Injective P.stateL :=
  P.boundary.weightedStateL_injective P.speed P.speed_continuous P.speed_pos

theorem RegularSturmProblem.stateL_compact (P : RegularSturmProblem ι l r) :
    IsCompactOperator P.stateL :=
  P.boundary.weightedStateL_compact P.speed P.speed_continuous

theorem RegularSturmProblem.stateL_denseRange (P : RegularSturmProblem ι l r) :
    DenseRange P.stateL :=
  P.boundary.weightedStateL_denseRange P.speed P.speed_continuous P.speed_pos

end TimeTraps.Analysis
