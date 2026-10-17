module

public import TimeTraps.Analysis.IntervalDirichletFormCoercive
public import TimeTraps.Analysis.IntervalDirichletDense
public import TimeTraps.Analysis.LaxMilgramOperator

@[expose] public section

/-! Actual L2 solution operators on the full zero-boundary Sobolev space.
The selected endpoint traces supply coercivity, including when the finite
family of nonnegative point contacts is empty. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

structure DirichletPointProblem (ι : Type*) [Fintype ι] (l r : ℝ) where
  boundary : IntervalDirichletBoundary l r
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : ι → ℝ
  strength_nonneg : ∀ i, 0 ≤ strength i
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc l r

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def DirichletPointProblem.form (P : DirichletPointProblem ι l r) :
    IntervalDirichletSpace P.boundary →L[ℝ] IntervalDirichletSpace P.boundary →L[ℝ] ℝ :=
  intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem

theorem DirichletPointProblem.form_coercive (P : DirichletPointProblem ι l r) :
    @IsCoercive (IntervalDirichletSpace P.boundary)
      (Submodule.seminormedAddCommGroup P.boundary.subspace)
      (Submodule.normedSpace P.boundary.subspace) P.form :=
  intervalDirichletPointForm_coercive P.boundary P.diffusivity_pos
    P.strength P.site P.strength_nonneg P.site_mem

def DirichletPointProblem.load (P : DirichletPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalDirichletSpace P.boundary →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalDirichletSpace P.boundary) :=
    Submodule.seminormedAddCommGroup P.boundary.subspace
  letI : NormedSpace ℝ (IntervalDirichletSpace P.boundary) :=
    Submodule.normedSpace P.boundary.subspace
  let i : IntervalDirichletSpace P.boundary →L[ℝ] IntervalSobolevSpace l r :=
    P.boundary.subspace.subtypeL
  exact ((intervalSobolevL2Load l r).flip.comp i).flip

theorem DirichletPointProblem.load_apply (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalDirichletSpace P.boundary) :
    P.load f v = inner ℝ f (P.boundary.stateL v) := rfl

def DirichletPointProblem.solution (P : DirichletPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalDirichletSpace P.boundary :=
  (coerciveFormSolutionL (V := IntervalDirichletSpace P.boundary) P.form P.form_coercive).comp P.load

def DirichletPointProblem.inverse (P : DirichletPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  P.boundary.stateL.comp P.solution

-- Normalizing the nested subspace instances in the generic solution theorem
-- requires a larger elaboration budget; the Hilbert space and form are unchanged.
set_option maxHeartbeats 800000 in
theorem DirichletPointProblem.solution_spec (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalDirichletSpace P.boundary) :
    P.form (P.solution f) v = inner ℝ f (P.boundary.stateL v) := by
  simpa only [DirichletPointProblem.solution, ContinuousLinearMap.comp_apply] using
    (coerciveFormSolutionL_spec (V := IntervalDirichletSpace P.boundary)
      P.form P.form_coercive (P.load f) v).trans (P.load_apply f v)

theorem DirichletPointProblem.inverse_apply (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : P.inverse f = P.boundary.stateL (P.solution f) := rfl

theorem DirichletPointProblem.inverse_compact (P : DirichletPointProblem ι l r) :
    IsCompactOperator P.inverse := P.boundary.stateL_compact.comp_clm P.solution

theorem DirichletPointProblem.form_symmetric (P : DirichletPointProblem ι l r)
    (u v : IntervalDirichletSpace P.boundary) : P.form u v = P.form v u :=
  intervalDirichletPointForm_symmetric P.boundary P.diffusivity P.strength P.site P.site_mem u v

theorem DirichletPointProblem.solution_eq_iff (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (u : IntervalDirichletSpace P.boundary) :
    u = P.solution f ↔ ∀ v : IntervalDirichletSpace P.boundary,
      P.form u v = inner ℝ f (P.boundary.stateL v) := by
  constructor
  · rintro rfl
    exact P.solution_spec f
  · intro h
    have he : P.form (u - P.solution f) (u - P.solution f) = 0 := by
      rw [map_sub P.form u (P.solution f), sub_apply, h, P.solution_spec, sub_self]
    obtain ⟨c, hc, hb⟩ := P.form_coercive
    have hle := hb (u - P.solution f)
    rw [he] at hle
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hn
    have hp : 0 < ‖u - P.solution f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hle

end

end TimeTraps.Analysis
