module

public import TimeTraps.Analysis.IntervalPeriodicProblem
public import TimeTraps.Analysis.GeneralIntervalPointWeak

@[expose] public section

/-! The actual periodic solution operator is characterized by every
independent AC/L2 energy test with matching endpoint values. Point contacts
at either endpoint remain in the physical pairing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem intervalPeriodicPointForm_ofEnergy
    (B : IntervalPeriodicBoundary l r) (D : ℝ) (κ z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (hup : u r = u l) (hvp : v r = v l) :
    intervalPeriodicPointForm B D κ z hz (B.ofEnergy hu hup) (B.ofEnergy hv hvp) =
      intervalPointForm D κ z l r u v := by
  rw [intervalPeriodicPointForm_apply]
  exact intervalPointForm_congr D κ z B.interval_pos.le hz
    (B.ofEnergy_representative hu hup) (B.ofEnergy_representative hv hvp)

theorem PeriodicPointProblem.load_representative (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalPeriodicSpace P.boundary) :
    P.load f v = ∫ x in l..r, f x * v.val.representative P.boundary.interval_pos x :=
  intervalSobolevL2Load_representative P.boundary.interval_pos f v.val

theorem PeriodicPointProblem.load_ofEnergy (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {v : ℝ → ℝ} (hv : IntervalEnergy v l r)
    (hvp : v l = v r) :
    P.load f (P.boundary.ofEnergy hv hvp.symm) = ∫ x in l..r, f x * v x :=
  intervalSobolevL2Load_ofEnergy P.boundary.interval_pos f hv

theorem PeriodicPointProblem.weak_iff (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hup : u l = u r) :
    (∀ v : IntervalPeriodicSpace P.boundary,
      P.form (P.boundary.ofEnergy hu hup.symm) v = inner ℝ f (P.boundary.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → v l = v r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv hvp
    have he := h (P.boundary.ofEnergy hv hvp.symm)
    change intervalPeriodicPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu hup.symm) (P.boundary.ofEnergy hv hvp.symm) =
      P.load f (P.boundary.ofEnergy hv hvp.symm) at he
    rwa [intervalPeriodicPointForm_ofEnergy, P.load_ofEnergy f hv hvp] at he
  · intro h v
    change intervalPeriodicPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu hup.symm) v = P.load f v
    rw [intervalPeriodicPointForm_apply, P.load_representative]
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le
      P.site_mem (P.boundary.ofEnergy_representative hu hup.symm) (fun _ _ => rfl)]
    exact h (v.val.representative P.boundary.interval_pos)
      (v.val.representative_spec P.boundary.interval_pos).1
      (P.boundary.representative_periodic v).symm

theorem PeriodicPointProblem.inverse_eq_iff_weak (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hup : u l = u r) :
    P.inverse f = P.boundary.stateL (P.boundary.ofEnergy hu hup.symm) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → v l = v r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  rw [← P.weak_iff f hu hup, ← P.solution_eq_iff f (P.boundary.ofEnergy hu hup.symm)]
  constructor
  · intro h
    exact (P.boundary.stateL_injective h).symm
  · intro h
    rw [h, P.inverse_apply]

theorem PeriodicPointProblem.solution_physical (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : ℝ → ℝ) (hv : IntervalEnergy v l r)
    (hvp : v l = v r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.solution f).val.representative P.boundary.interval_pos) v =
        ∫ x in l..r, f x * v x := by
  have hu := ((P.solution f).val.representative_spec P.boundary.interval_pos).1
  apply (P.weak_iff f hu (P.boundary.representative_periodic (P.solution f)).symm).mp _ v hv hvp
  rw [P.boundary.ofEnergy_representative_eq]
  exact P.solution_spec f

end TimeTraps.Analysis
