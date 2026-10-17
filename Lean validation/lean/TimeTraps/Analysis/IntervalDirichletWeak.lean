module

public import TimeTraps.Analysis.IntervalDirichletProblem
public import TimeTraps.Analysis.IntervalDirichletFormPhysical
public import TimeTraps.Analysis.GeneralIntervalPointWeak

@[expose] public section

/-! The actual absorbing-endpoint operator and every physical zero-trace
AC/L2 test function. The test space is the full independent Dirichlet H1
space, including the case of no point contacts. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem IntervalDirichletBoundary.ofEnergy_representative_eq
    (B : IntervalDirichletBoundary l r) (u : IntervalDirichletSpace B) :
    B.ofEnergy ((u.val.representative_spec B.interval_pos).1)
      (fun _ hx => B.representative_zero u hx) = u := by
  apply Subtype.ext
  exact IntervalSobolevSpace.ofEnergy_representative u.val B.interval_pos

theorem DirichletPointProblem.load_representative (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalDirichletSpace P.boundary) :
    P.load f v = ∫ x in l..r, f x * v.val.representative P.boundary.interval_pos x :=
  intervalSobolevL2Load_representative P.boundary.interval_pos f v.val

theorem DirichletPointProblem.load_ofEnergy (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {v : ℝ → ℝ} (hv : IntervalEnergy v l r)
    (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0) :
    P.load f (P.boundary.ofEnergy hv hvz) = ∫ x in l..r, f x * v x :=
  intervalSobolevL2Load_ofEnergy P.boundary.interval_pos f hv

theorem DirichletPointProblem.weak_iff (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    (∀ v : IntervalDirichletSpace P.boundary,
      P.form (P.boundary.ofEnergy hu huz) v = inner ℝ f (P.boundary.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv hvz
    have he := h (P.boundary.ofEnergy hv hvz)
    change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hv hvz) =
      P.load f (P.boundary.ofEnergy hv hvz) at he
    rwa [intervalDirichletPointForm_ofEnergy, P.load_ofEnergy] at he
  · intro h v
    change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu huz) v = P.load f v
    rw [intervalDirichletPointForm_apply, P.load_representative]
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le
      P.site_mem (P.boundary.ofEnergy_representative hu huz) (fun _ _ => rfl)]
    exact h (v.val.representative P.boundary.interval_pos)
      (v.val.representative_spec P.boundary.interval_pos).1 (fun _ hx => P.boundary.representative_zero v hx)

theorem DirichletPointProblem.inverse_eq_iff_weak (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    P.inverse f = P.boundary.stateL (P.boundary.ofEnergy hu huz) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  rw [← P.weak_iff f hu huz, ← P.solution_eq_iff f (P.boundary.ofEnergy hu huz)]
  constructor
  · intro h
    exact (P.boundary.stateL_injective h).symm
  · intro h
    rw [h, P.inverse_apply]

theorem DirichletPointProblem.solution_physical (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : ℝ → ℝ) (hv : IntervalEnergy v l r)
    (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.solution f).val.representative P.boundary.interval_pos) v =
        ∫ x in l..r, f x * v x := by
  have hu := ((P.solution f).val.representative_spec P.boundary.interval_pos).1
  apply (P.weak_iff f hu (fun _ hx => P.boundary.representative_zero (P.solution f) hx)).mp _ v hv hvz
  rw [P.boundary.ofEnergy_representative_eq]
  exact P.solution_spec f

end TimeTraps.Analysis
