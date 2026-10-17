module

public import TimeTraps.Analysis.SignedDirichletPointForm
public import TimeTraps.Analysis.IntervalDirichletDense
public import TimeTraps.Analysis.LaxMilgramOperator

@[expose] public section

/-! The actual shifted L2 solution for arbitrary real point contacts on
the full selected-zero H1 space. Coercivity follows from a positive mass
shift; neither nonnegative contacts nor a nonempty contact family is assumed. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

structure SignedDirichletPointProblem (ι : Type*) [Fintype ι] (l r : ℝ) where
  boundary : IntervalDirichletBoundary l r
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : ι → ℝ
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc l r

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def SignedDirichletPointProblem.massShift (P : SignedDirichletPointProblem ι l r) : ℝ :=
  intervalPointNegativeBound P.diffusivity P.strength l r + 1

theorem SignedDirichletPointProblem.massShift_pos (P : SignedDirichletPointProblem ι l r) :
    0 < P.massShift := by
  have h := intervalPointNegativeBound_nonneg P.diffusivity_pos P.boundary.interval_pos P.strength
  change 0 < intervalPointNegativeBound P.diffusivity P.strength l r + 1
  linarith

def SignedDirichletPointProblem.form (P : SignedDirichletPointProblem ι l r) :
    IntervalDirichletSpace P.boundary →L[ℝ] IntervalDirichletSpace P.boundary →L[ℝ] ℝ :=
  intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem

def SignedDirichletPointProblem.shiftedForm (P : SignedDirichletPointProblem ι l r) :
    IntervalDirichletSpace P.boundary →L[ℝ] IntervalDirichletSpace P.boundary →L[ℝ] ℝ :=
  intervalDirichletShiftedPointForm P.boundary P.diffusivity P.strength P.site P.site_mem P.massShift

theorem SignedDirichletPointProblem.shiftedForm_coercive (P : SignedDirichletPointProblem ι l r) :
    @IsCoercive (IntervalDirichletSpace P.boundary)
      (Submodule.seminormedAddCommGroup P.boundary.subspace)
      (Submodule.normedSpace P.boundary.subspace) P.shiftedForm :=
  intervalDirichletShiftedPointForm_coercive P.boundary P.diffusivity_pos
    P.strength P.site P.site_mem

def SignedDirichletPointProblem.load (P : SignedDirichletPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalDirichletSpace P.boundary →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalDirichletSpace P.boundary) :=
    Submodule.seminormedAddCommGroup P.boundary.subspace
  letI : NormedSpace ℝ (IntervalDirichletSpace P.boundary) :=
    Submodule.normedSpace P.boundary.subspace
  let i : IntervalDirichletSpace P.boundary →L[ℝ] IntervalSobolevSpace l r :=
    P.boundary.subspace.subtypeL
  exact ((intervalSobolevL2Load l r).flip.comp i).flip

theorem SignedDirichletPointProblem.load_apply (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalDirichletSpace P.boundary) :
    P.load f v = inner ℝ f (P.boundary.stateL v) := rfl

def SignedDirichletPointProblem.shiftedSolution (P : SignedDirichletPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalDirichletSpace P.boundary :=
  (coerciveFormSolutionL (V := IntervalDirichletSpace P.boundary) P.shiftedForm P.shiftedForm_coercive).comp P.load

def SignedDirichletPointProblem.shiftedInverse (P : SignedDirichletPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  P.boundary.stateL.comp P.shiftedSolution

-- Normalizing the nested subspace instances in the generic solution theorem
-- requires a larger elaboration budget; the Hilbert space and form are unchanged.
set_option maxHeartbeats 800000 in
theorem SignedDirichletPointProblem.shiftedSolution_spec (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalDirichletSpace P.boundary) :
    P.shiftedForm (P.shiftedSolution f) v = inner ℝ f (P.boundary.stateL v) := by
  simpa only [SignedDirichletPointProblem.shiftedSolution, ContinuousLinearMap.comp_apply] using
    (coerciveFormSolutionL_spec (V := IntervalDirichletSpace P.boundary)
      P.shiftedForm P.shiftedForm_coercive (P.load f) v).trans (P.load_apply f v)

theorem SignedDirichletPointProblem.shiftedInverse_apply (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : P.shiftedInverse f = P.boundary.stateL (P.shiftedSolution f) := rfl

theorem SignedDirichletPointProblem.shiftedInverse_compact (P : SignedDirichletPointProblem ι l r) :
    IsCompactOperator P.shiftedInverse := P.boundary.stateL_compact.comp_clm P.shiftedSolution

theorem SignedDirichletPointProblem.shiftedForm_symmetric (P : SignedDirichletPointProblem ι l r)
    (u v : IntervalDirichletSpace P.boundary) : P.shiftedForm u v = P.shiftedForm v u :=
  intervalDirichletShiftedPointForm_symmetric P.boundary P.diffusivity P.strength P.site P.site_mem P.massShift u v

theorem SignedDirichletPointProblem.shiftedSolution_eq_iff (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (u : IntervalDirichletSpace P.boundary) :
    u = P.shiftedSolution f ↔ ∀ v : IntervalDirichletSpace P.boundary,
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
