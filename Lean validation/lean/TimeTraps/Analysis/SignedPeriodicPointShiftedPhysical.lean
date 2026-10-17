module

public import TimeTraps.Analysis.SignedPeriodicPointPhysical
public import TimeTraps.Analysis.SignedIntervalPointWeak

@[expose] public section

/-! Solvability and uniqueness of the shifted equation in the original
physical endpoint-matched periodic H1 class. The mass shift remains explicit, and
every admissible physical test is included. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem intervalPeriodicShiftedPointForm_ofEnergy (B : IntervalPeriodicBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    {u v : ℝ → ℝ} (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : u l = u r) (hvz : v l = v r) :
    intervalPeriodicShiftedPointForm B D κ z hz c (B.ofEnergy hu huz.symm) (B.ofEnergy hv hvz.symm) =
      intervalPointForm D κ z l r u v + c * ∫ x in l..r, u x * v x :=
  intervalSobolevShiftedPointForm_ofEnergy B.interval_pos D κ z hz c hu hv

theorem SignedPeriodicPointProblem.shifted_weak_iff (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : u l = u r) :
    (∀ v : IntervalPeriodicSpace P.boundary,
      P.shiftedForm (P.boundary.ofEnergy hu huz.symm) v = inner ℝ f (P.boundary.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (v l = v r) →
      intervalPointForm P.diffusivity P.strength P.site l r u v +
        P.massShift * (∫ x in l..r, u x * v x) = ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv hvz
    have he := h (P.boundary.ofEnergy hv hvz.symm)
    change intervalPeriodicShiftedPointForm P.boundary P.diffusivity P.strength P.site
      P.site_mem P.massShift (P.boundary.ofEnergy hu huz.symm) (P.boundary.ofEnergy hv hvz.symm) =
        P.load f (P.boundary.ofEnergy hv hvz.symm) at he
    rwa [intervalPeriodicShiftedPointForm_ofEnergy P.boundary P.diffusivity P.strength
      P.site P.site_mem P.massShift hu hv huz hvz, P.load_ofEnergy f hv hvz] at he
  · intro h v
    change intervalSobolevShiftedPointForm P.boundary.interval_pos P.diffusivity P.strength P.site
      P.site_mem P.massShift (ofEnergy hu P.boundary.interval_pos) v.val =
        intervalSobolevL2Load l r f v.val
    rw [intervalSobolevShiftedPointForm_apply,
      intervalSobolevL2Load_representative P.boundary.interval_pos,
      intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le P.site_mem
        (representative_ofEnergy hu P.boundary.interval_pos) (fun _ _ => rfl)]
    have hm : (∫ x in l..r, (ofEnergy hu P.boundary.interval_pos).representative P.boundary.interval_pos x *
        v.val.representative P.boundary.interval_pos x) =
        ∫ x in l..r, u x * v.val.representative P.boundary.interval_pos x := by
      apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
      intro x hx
      change (ofEnergy hu P.boundary.interval_pos).representative P.boundary.interval_pos x *
        v.val.representative P.boundary.interval_pos x = u x * v.val.representative P.boundary.interval_pos x
      rw [representative_ofEnergy hu P.boundary.interval_pos (Ioo_subset_Icc_self hx)]
    rw [hm]
    exact h (v.val.representative P.boundary.interval_pos)
      (v.val.representative_spec P.boundary.interval_pos).1
      (P.boundary.representative_periodic v).symm

theorem SignedPeriodicPointProblem.shiftedInverse_eq_iff_weak
    (P : SignedPeriodicPointProblem ι l r) (f : IntervalSobolevL2 l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : u l = u r) :
    P.shiftedInverse f = P.boundary.stateL (P.boundary.ofEnergy hu huz.symm) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (v l = v r) →
      intervalPointForm P.diffusivity P.strength P.site l r u v +
        P.massShift * (∫ x in l..r, u x * v x) = ∫ x in l..r, f x * v x) := by
  rw [← P.shifted_weak_iff f hu huz,
    ← P.shiftedSolution_eq_iff f (P.boundary.ofEnergy hu huz.symm)]
  constructor
  · intro h
    exact (P.boundary.stateL_injective h).symm
  · intro h
    rw [h, P.shiftedInverse_apply]

theorem SignedPeriodicPointProblem.shiftedSolution_physical
    (P : SignedPeriodicPointProblem ι l r) (f : IntervalSobolevL2 l r)
    (v : ℝ → ℝ) (hv : IntervalEnergy v l r) (hvz : v l = v r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.shiftedSolution f).val.representative P.boundary.interval_pos) v +
        P.massShift * (∫ x in l..r, (P.shiftedSolution f).val.representative P.boundary.interval_pos x * v x) =
          ∫ x in l..r, f x * v x := by
  have hu := ((P.shiftedSolution f).val.representative_spec P.boundary.interval_pos).1
  apply (P.shifted_weak_iff f hu
    (P.boundary.representative_periodic (P.shiftedSolution f)).symm).mp _ v hv hvz
  rw [P.boundary.ofEnergy_representative_eq]
  exact P.shiftedSolution_spec f

theorem SignedPeriodicPointProblem.shifted_physical_unique
    (P : SignedPeriodicPointProblem ι l r) (f : IntervalSobolevL2 l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : u l = u r)
    (hvz : v l = v r)
    (heu : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (w l = w r) →
      intervalPointForm P.diffusivity P.strength P.site l r u w +
        P.massShift * (∫ x in l..r, u x * w x) = ∫ x in l..r, f x * w x)
    (hev : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (w l = w r) →
      intervalPointForm P.diffusivity P.strength P.site l r v w +
        P.massShift * (∫ x in l..r, v x * w x) = ∫ x in l..r, f x * w x) :
    EqOn u v (Icc l r) := by
  have h1 := (P.shiftedSolution_eq_iff f (P.boundary.ofEnergy hu huz.symm)).mpr
    ((P.shifted_weak_iff f hu huz).mpr heu)
  have h2 := (P.shiftedSolution_eq_iff f (P.boundary.ofEnergy hv hvz.symm)).mpr
    ((P.shifted_weak_iff f hv hvz).mpr hev)
  have he : P.boundary.ofEnergy hu huz.symm = P.boundary.ofEnergy hv hvz.symm := h1.trans h2.symm
  intro x hx
  calc
    u x = (P.boundary.ofEnergy hu huz.symm).val.representative P.boundary.interval_pos x :=
      (P.boundary.ofEnergy_representative hu huz.symm hx).symm
    _ = (P.boundary.ofEnergy hv hvz.symm).val.representative P.boundary.interval_pos x := by rw [he]
    _ = v x := P.boundary.ofEnergy_representative hv hvz.symm hx

end TimeTraps.Analysis
