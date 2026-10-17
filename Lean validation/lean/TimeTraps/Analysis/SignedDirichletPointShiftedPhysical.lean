module

public import TimeTraps.Analysis.SignedDirichletPointPhysical
public import TimeTraps.Analysis.SignedIntervalPointWeak

@[expose] public section

/-! Solvability and uniqueness of the shifted equation in the original
physical selected-zero H1 class. The mass shift remains explicit, and
every admissible physical test is included. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem intervalDirichletShiftedPointForm_ofEnergy (B : IntervalDirichletBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    {u v : ℝ → ℝ} (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : ∀ x ∈ B.zero_sites, u x = 0) (hvz : ∀ x ∈ B.zero_sites, v x = 0) :
    intervalDirichletShiftedPointForm B D κ z hz c (B.ofEnergy hu huz) (B.ofEnergy hv hvz) =
      intervalPointForm D κ z l r u v + c * ∫ x in l..r, u x * v x :=
  intervalSobolevShiftedPointForm_ofEnergy B.interval_pos D κ z hz c hu hv

theorem SignedDirichletPointProblem.shifted_weak_iff (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    (∀ v : IntervalDirichletSpace P.boundary,
      P.shiftedForm (P.boundary.ofEnergy hu huz) v = inner ℝ f (P.boundary.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v +
        P.massShift * (∫ x in l..r, u x * v x) = ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv hvz
    have he := h (P.boundary.ofEnergy hv hvz)
    change intervalDirichletShiftedPointForm P.boundary P.diffusivity P.strength P.site
      P.site_mem P.massShift (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hv hvz) =
        P.load f (P.boundary.ofEnergy hv hvz) at he
    rwa [intervalDirichletShiftedPointForm_ofEnergy, P.load_ofEnergy] at he
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
      (fun _ hx => P.boundary.representative_zero v hx)

theorem SignedDirichletPointProblem.shiftedInverse_eq_iff_weak
    (P : SignedDirichletPointProblem ι l r) (f : IntervalSobolevL2 l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    P.shiftedInverse f = P.boundary.stateL (P.boundary.ofEnergy hu huz) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v +
        P.massShift * (∫ x in l..r, u x * v x) = ∫ x in l..r, f x * v x) := by
  rw [← P.shifted_weak_iff f hu huz,
    ← P.shiftedSolution_eq_iff f (P.boundary.ofEnergy hu huz)]
  constructor
  · intro h
    exact (P.boundary.stateL_injective h).symm
  · intro h
    rw [h, P.shiftedInverse_apply]

theorem SignedDirichletPointProblem.shiftedSolution_physical
    (P : SignedDirichletPointProblem ι l r) (f : IntervalSobolevL2 l r)
    (v : ℝ → ℝ) (hv : IntervalEnergy v l r) (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.shiftedSolution f).val.representative P.boundary.interval_pos) v +
        P.massShift * (∫ x in l..r, (P.shiftedSolution f).val.representative P.boundary.interval_pos x * v x) =
          ∫ x in l..r, f x * v x := by
  have hu := ((P.shiftedSolution f).val.representative_spec P.boundary.interval_pos).1
  apply (P.shifted_weak_iff f hu
    (fun _ hx => P.boundary.representative_zero (P.shiftedSolution f) hx)).mp _ v hv hvz
  rw [P.boundary.ofEnergy_representative_eq]
  exact P.shiftedSolution_spec f

theorem SignedDirichletPointProblem.shifted_physical_unique
    (P : SignedDirichletPointProblem ι l r) (f : IntervalSobolevL2 l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0)
    (heu : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (∀ x ∈ P.boundary.zero_sites, w x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u w +
        P.massShift * (∫ x in l..r, u x * w x) = ∫ x in l..r, f x * w x)
    (hev : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (∀ x ∈ P.boundary.zero_sites, w x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r v w +
        P.massShift * (∫ x in l..r, v x * w x) = ∫ x in l..r, f x * w x) :
    EqOn u v (Icc l r) := by
  have h1 := (P.shiftedSolution_eq_iff f (P.boundary.ofEnergy hu huz)).mpr
    ((P.shifted_weak_iff f hu huz).mpr heu)
  have h2 := (P.shiftedSolution_eq_iff f (P.boundary.ofEnergy hv hvz)).mpr
    ((P.shifted_weak_iff f hv hvz).mpr hev)
  have he : P.boundary.ofEnergy hu huz = P.boundary.ofEnergy hv hvz := h1.trans h2.symm
  intro x hx
  calc
    u x = (P.boundary.ofEnergy hu huz).val.representative P.boundary.interval_pos x :=
      (P.boundary.ofEnergy_representative hu huz hx).symm
    _ = (P.boundary.ofEnergy hv hvz).val.representative P.boundary.interval_pos x := by rw [he]
    _ = v x := P.boundary.ofEnergy_representative hv hvz hx

end TimeTraps.Analysis
