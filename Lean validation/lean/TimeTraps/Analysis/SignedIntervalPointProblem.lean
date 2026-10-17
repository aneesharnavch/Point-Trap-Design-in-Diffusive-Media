module

public import TimeTraps.Analysis.IntervalPointFormSemiboundedHilbert
public import TimeTraps.Analysis.LaxMilgramOperator
public import TimeTraps.Analysis.IntervalSobolevCompactL2
public import TimeTraps.Analysis.IntervalSobolevDense

@[expose] public section

/-! The actual mass-shifted solution for finite real point interactions.
The strengths are arbitrary real numbers and the contact family may be
empty. Every construction here retains the explicit positive mass shift. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

structure SignedIntervalPointProblem (ι : Type*) [Fintype ι] (l r : ℝ) where
  interval_pos : l < r
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : ι → ℝ
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc l r

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def SignedIntervalPointProblem.massShift (P : SignedIntervalPointProblem ι l r) : ℝ :=
  intervalPointNegativeBound P.diffusivity P.strength l r + 1

theorem SignedIntervalPointProblem.massShift_pos (P : SignedIntervalPointProblem ι l r) :
    0 < P.massShift := by
  have h := intervalPointNegativeBound_nonneg P.diffusivity_pos P.interval_pos P.strength
  change 0 < intervalPointNegativeBound P.diffusivity P.strength l r + 1
  linarith

def SignedIntervalPointProblem.shiftedForm (P : SignedIntervalPointProblem ι l r) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  intervalSobolevShiftedPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem P.massShift

theorem SignedIntervalPointProblem.shiftedForm_coercive (P : SignedIntervalPointProblem ι l r) :
    IsCoercive P.shiftedForm :=
  intervalSobolevShiftedPointForm_coercive P.interval_pos P.diffusivity_pos
    P.strength P.site P.site_mem

def SignedIntervalPointProblem.shiftedSolution (P : SignedIntervalPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevSpace l r :=
  (coerciveFormSolutionL P.shiftedForm P.shiftedForm_coercive).comp (intervalSobolevL2Load l r)

def SignedIntervalPointProblem.shiftedInverse (P : SignedIntervalPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  (stateL l r).comp P.shiftedSolution

theorem SignedIntervalPointProblem.shiftedSolution_spec (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalSobolevSpace l r) :
    P.shiftedForm (P.shiftedSolution f) v = inner ℝ f v.state :=
  coerciveFormSolutionL_spec P.shiftedForm P.shiftedForm_coercive (intervalSobolevL2Load l r f) v

theorem SignedIntervalPointProblem.shiftedInverse_apply (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : P.shiftedInverse f = (P.shiftedSolution f).state := rfl

theorem SignedIntervalPointProblem.shiftedInverse_compact (P : SignedIntervalPointProblem ι l r) :
    IsCompactOperator P.shiftedInverse :=
  (stateL_isCompact P.interval_pos).comp_clm P.shiftedSolution

theorem SignedIntervalPointProblem.shiftedForm_symmetric (P : SignedIntervalPointProblem ι l r)
    (u v : IntervalSobolevSpace l r) : P.shiftedForm u v = P.shiftedForm v u :=
  intervalSobolevShiftedPointForm_symmetric P.interval_pos P.diffusivity P.strength P.site
    P.site_mem P.massShift u v

theorem SignedIntervalPointProblem.shiftedSolution_eq_iff (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (u : IntervalSobolevSpace l r) :
    u = P.shiftedSolution f ↔
      ∀ v : IntervalSobolevSpace l r, P.shiftedForm u v = inner ℝ f v.state := by
  constructor
  · rintro rfl
    exact P.shiftedSolution_spec f
  · intro h
    apply P.shiftedForm_coercive.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [P.shiftedForm_coercive.continuousLinearEquivOfBilin_apply,
      P.shiftedForm_coercive.continuousLinearEquivOfBilin_apply, h, P.shiftedSolution_spec]

end

end TimeTraps.Analysis
