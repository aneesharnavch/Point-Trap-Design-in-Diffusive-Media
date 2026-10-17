module

public import TimeTraps.Analysis.SignedPeriodicPointForm
public import TimeTraps.Analysis.IntervalPeriodicDense
public import TimeTraps.Analysis.LaxMilgramOperator

@[expose] public section

/-! The actual shifted L2 solution for arbitrary real point contacts on
the full endpoint-matched periodic H1 space. Coercivity follows from a positive mass
shift; neither nonnegative contacts nor a nonempty contact family is assumed. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

structure SignedPeriodicPointProblem (ι : Type*) [Fintype ι] (l r : ℝ) where
  boundary : IntervalPeriodicBoundary l r
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : ι → ℝ
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc l r

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def SignedPeriodicPointProblem.massShift (P : SignedPeriodicPointProblem ι l r) : ℝ :=
  intervalPointNegativeBound P.diffusivity P.strength l r + 1

theorem SignedPeriodicPointProblem.massShift_pos (P : SignedPeriodicPointProblem ι l r) :
    0 < P.massShift := by
  have h := intervalPointNegativeBound_nonneg P.diffusivity_pos P.boundary.interval_pos P.strength
  change 0 < intervalPointNegativeBound P.diffusivity P.strength l r + 1
  linarith

def SignedPeriodicPointProblem.form (P : SignedPeriodicPointProblem ι l r) :
    IntervalPeriodicSpace P.boundary →L[ℝ] IntervalPeriodicSpace P.boundary →L[ℝ] ℝ :=
  intervalPeriodicPointForm P.boundary P.diffusivity P.strength P.site P.site_mem

def SignedPeriodicPointProblem.shiftedForm (P : SignedPeriodicPointProblem ι l r) :
    IntervalPeriodicSpace P.boundary →L[ℝ] IntervalPeriodicSpace P.boundary →L[ℝ] ℝ :=
  intervalPeriodicShiftedPointForm P.boundary P.diffusivity P.strength P.site P.site_mem P.massShift

theorem SignedPeriodicPointProblem.shiftedForm_coercive (P : SignedPeriodicPointProblem ι l r) :
    @IsCoercive (IntervalPeriodicSpace P.boundary)
      (Submodule.seminormedAddCommGroup P.boundary.subspace)
      (Submodule.normedSpace P.boundary.subspace) P.shiftedForm :=
  intervalPeriodicShiftedPointForm_coercive P.boundary P.diffusivity_pos
    P.strength P.site P.site_mem

def SignedPeriodicPointProblem.load (P : SignedPeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalPeriodicSpace P.boundary →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalPeriodicSpace P.boundary) :=
    Submodule.seminormedAddCommGroup P.boundary.subspace
  letI : NormedSpace ℝ (IntervalPeriodicSpace P.boundary) :=
    Submodule.normedSpace P.boundary.subspace
  let i : IntervalPeriodicSpace P.boundary →L[ℝ] IntervalSobolevSpace l r :=
    P.boundary.subspace.subtypeL
  exact ((intervalSobolevL2Load l r).flip.comp i).flip

theorem SignedPeriodicPointProblem.load_apply (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalPeriodicSpace P.boundary) :
    P.load f v = inner ℝ f (P.boundary.stateL v) := rfl

def SignedPeriodicPointProblem.shiftedSolution (P : SignedPeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalPeriodicSpace P.boundary :=
  (coerciveFormSolutionL (V := IntervalPeriodicSpace P.boundary) P.shiftedForm P.shiftedForm_coercive).comp P.load

def SignedPeriodicPointProblem.shiftedInverse (P : SignedPeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  P.boundary.stateL.comp P.shiftedSolution

-- Normalizing the nested subspace instances in the generic solution theorem
-- requires a larger elaboration budget; the Hilbert space and form are unchanged.
set_option maxHeartbeats 800000 in
theorem SignedPeriodicPointProblem.shiftedSolution_spec (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalPeriodicSpace P.boundary) :
    P.shiftedForm (P.shiftedSolution f) v = inner ℝ f (P.boundary.stateL v) := by
  simpa only [SignedPeriodicPointProblem.shiftedSolution, ContinuousLinearMap.comp_apply] using
    (coerciveFormSolutionL_spec (V := IntervalPeriodicSpace P.boundary)
      P.shiftedForm P.shiftedForm_coercive (P.load f) v).trans (P.load_apply f v)

theorem SignedPeriodicPointProblem.shiftedInverse_apply (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : P.shiftedInverse f = P.boundary.stateL (P.shiftedSolution f) := rfl

theorem SignedPeriodicPointProblem.shiftedInverse_compact (P : SignedPeriodicPointProblem ι l r) :
    IsCompactOperator P.shiftedInverse := P.boundary.stateL_compact.comp_clm P.shiftedSolution

theorem SignedPeriodicPointProblem.shiftedForm_symmetric (P : SignedPeriodicPointProblem ι l r)
    (u v : IntervalPeriodicSpace P.boundary) : P.shiftedForm u v = P.shiftedForm v u :=
  intervalPeriodicShiftedPointForm_symmetric P.boundary P.diffusivity P.strength P.site P.site_mem P.massShift u v

theorem SignedPeriodicPointProblem.shiftedSolution_eq_iff (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (u : IntervalPeriodicSpace P.boundary) :
    u = P.shiftedSolution f ↔ ∀ v : IntervalPeriodicSpace P.boundary,
      P.shiftedForm u v = inner ℝ f (P.boundary.stateL v) := by
  constructor
  · rintro rfl
    exact P.shiftedSolution_spec f
  · intro h
    have he : P.shiftedForm (u - P.shiftedSolution f) (u - P.shiftedSolution f) = 0 := by
      rw [map_sub P.shiftedForm u (P.shiftedSolution f), sub_apply, h, P.shiftedSolution_spec, sub_self]
    obtain ⟨c, hc, hb⟩ := P.shiftedForm_coercive
    have hle := hb (u - P.shiftedSolution f)
    rw [he] at hle
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hn
    have hp : 0 < ‖u - P.shiftedSolution f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hle

end

end TimeTraps.Analysis
