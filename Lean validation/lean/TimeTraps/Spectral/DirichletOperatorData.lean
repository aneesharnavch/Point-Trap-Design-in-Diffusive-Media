module

public import TimeTraps.Spectral.DirichletRayleigh
public import TimeTraps.Analysis.IntervalDirichletProblem
public import TimeTraps.Analysis.IntervalDirichletFormPhysical

@[expose] public section

/-! The original absorbing-interval data as an actual zero-boundary point
problem with an empty contact family. The selected traces are exactly the
original left, right, or both absorbing conditions. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

noncomputable def DirichletInterval.operatorBoundary (P : DirichletInterval) :
    IntervalDirichletBoundary 0 P.length := by
  classical
  exact {
    interval_pos := P.length_pos
    zero_sites := match P.ends with
      | .left => {0}
      | .right => {P.length}
      | .both => {0, P.length}
    nonempty := by cases P.ends <;> simp
    boundary_only := by
      intro x hx
      cases he : P.ends <;> simp_all
  }

noncomputable def DirichletInterval.dirichletPointProblem (P : DirichletInterval) :
    DirichletPointProblem Empty 0 P.length where
  boundary := P.operatorBoundary
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := Empty.elim
  strength_nonneg := fun i => nomatch i
  site := Empty.elim
  site_mem := fun i => nomatch i

theorem DirichletInterval.operator_zeroTraces_iff (P : DirichletInterval) (v : ℝ → ℝ) :
    (∀ x ∈ P.operatorBoundary.zero_sites, v x = 0) ↔ P.zeroTraces v := by
  cases he : P.ends <;> simp [operatorBoundary, zeroTraces, he]

theorem DirichletInterval.operator_admissible (P : DirichletInterval)
    (u : IntervalDirichletSpace P.operatorBoundary) :
    P.admissible (u.val.representative P.length_pos) :=
  ⟨(u.val.representative_spec P.length_pos).1,
    (P.operator_zeroTraces_iff _).mp (fun _ hx => P.operatorBoundary.representative_zero u hx)⟩

noncomputable def DirichletInterval.operatorOfAdmissible (P : DirichletInterval)
    {u : ℝ → ℝ} (hu : P.admissible u) : IntervalDirichletSpace P.operatorBoundary :=
  P.operatorBoundary.ofEnergy hu.1 ((P.operator_zeroTraces_iff u).mpr hu.2)

theorem DirichletInterval.operatorOfAdmissible_representative (P : DirichletInterval)
    {u : ℝ → ℝ} (hu : P.admissible u) :
    EqOn ((P.operatorOfAdmissible hu).val.representative P.length_pos) u
      (Icc (0 : ℝ) P.length) :=
  P.operatorBoundary.ofEnergy_representative hu.1 ((P.operator_zeroTraces_iff u).mpr hu.2)

theorem DirichletInterval.operator_form_empty (P : DirichletInterval) (u v : ℝ → ℝ) :
    intervalPointForm P.dirichletPointProblem.diffusivity P.dirichletPointProblem.strength
      P.dirichletPointProblem.site 0 P.length u v =
        P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) := by
  simp [intervalPointForm, dirichletPointProblem]

theorem DirichletInterval.operator_squareMass (P : DirichletInterval)
    (u : IntervalDirichletSpace P.operatorBoundary) :
    P.squareMass (u.val.representative P.length_pos) = ‖P.operatorBoundary.stateL u‖ ^ 2 := by
  change P.squareMass (u.val.representative P.length_pos) = ‖u.val.state‖ ^ 2
  rw [DirichletInterval.squareMass, ← real_inner_self_eq_norm_sq, state_inner _ _ P.length_pos]
  simp only [pow_two]

end TimeTraps.Spectral
