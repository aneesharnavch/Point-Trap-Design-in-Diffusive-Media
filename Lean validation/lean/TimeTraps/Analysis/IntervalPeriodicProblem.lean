module

public import TimeTraps.Analysis.IntervalPeriodicForm
public import TimeTraps.Analysis.IntervalPeriodicDense
public import TimeTraps.Analysis.LaxMilgramOperator

@[expose] public section

/-! Actual L2 solution operators on the full periodic Sobolev space.
Positive diffusivity and a positive contact supply coercivity; the two
endpoint state traces agree throughout the independent Hilbert domain. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

structure PeriodicPointProblem (ι : Type*) [Fintype ι] (l r : ℝ) where
  boundary : IntervalPeriodicBoundary l r
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : ι → ℝ
  strength_nonneg : ∀ i, 0 ≤ strength i
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc l r
  positive_contact : ∃ i, 0 < strength i

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def PeriodicPointProblem.form (P : PeriodicPointProblem ι l r) :
    IntervalPeriodicSpace P.boundary →L[ℝ] IntervalPeriodicSpace P.boundary →L[ℝ] ℝ :=
  intervalPeriodicPointForm P.boundary P.diffusivity P.strength P.site P.site_mem

theorem PeriodicPointProblem.form_coercive (P : PeriodicPointProblem ι l r) :
    @IsCoercive (IntervalPeriodicSpace P.boundary)
      (Submodule.seminormedAddCommGroup P.boundary.subspace)
      (Submodule.normedSpace P.boundary.subspace) P.form := by
  obtain ⟨k, hk⟩ := P.positive_contact
  exact intervalPeriodicPointForm_coercive P.boundary P.diffusivity_pos
    P.strength P.site P.strength_nonneg P.site_mem k hk

def PeriodicPointProblem.load (P : PeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalPeriodicSpace P.boundary →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalPeriodicSpace P.boundary) :=
    Submodule.seminormedAddCommGroup P.boundary.subspace
  letI : NormedSpace ℝ (IntervalPeriodicSpace P.boundary) :=
    Submodule.normedSpace P.boundary.subspace
  let i : IntervalPeriodicSpace P.boundary →L[ℝ] IntervalSobolevSpace l r :=
    P.boundary.subspace.subtypeL
  exact ((intervalSobolevL2Load l r).flip.comp i).flip

theorem PeriodicPointProblem.load_apply (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalPeriodicSpace P.boundary) :
    P.load f v = inner ℝ f (P.boundary.stateL v) := rfl

def PeriodicPointProblem.solution (P : PeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalPeriodicSpace P.boundary :=
  (coerciveFormSolutionL (V := IntervalPeriodicSpace P.boundary) P.form P.form_coercive).comp P.load

def PeriodicPointProblem.inverse (P : PeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  P.boundary.stateL.comp P.solution

-- The nested Hilbert-subspace instances require extra normalization in this
-- generic solution theorem; the bound changes only elaboration resources.
set_option maxHeartbeats 800000 in
theorem PeriodicPointProblem.solution_spec (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalPeriodicSpace P.boundary) :
    P.form (P.solution f) v = inner ℝ f (P.boundary.stateL v) := by
  simpa only [PeriodicPointProblem.solution, ContinuousLinearMap.comp_apply] using
    (coerciveFormSolutionL_spec (V := IntervalPeriodicSpace P.boundary)
      P.form P.form_coercive (P.load f) v).trans (P.load_apply f v)

theorem PeriodicPointProblem.inverse_apply (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : P.inverse f = P.boundary.stateL (P.solution f) := rfl

theorem PeriodicPointProblem.inverse_compact (P : PeriodicPointProblem ι l r) :
    IsCompactOperator P.inverse := P.boundary.stateL_compact.comp_clm P.solution

theorem PeriodicPointProblem.form_symmetric (P : PeriodicPointProblem ι l r)
    (u v : IntervalPeriodicSpace P.boundary) : P.form u v = P.form v u :=
  intervalPeriodicPointForm_symmetric P.boundary P.diffusivity P.strength P.site P.site_mem u v

theorem PeriodicPointProblem.solution_eq_iff (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (u : IntervalPeriodicSpace P.boundary) :
    u = P.solution f ↔ ∀ v : IntervalPeriodicSpace P.boundary,
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
