module

public import TimeTraps.Analysis.SignedIntervalPointPositive
public import TimeTraps.Analysis.GeneralIntervalPointWeak

@[expose] public section

/-! The shifted equation against every signed physical H1 test, and
uniqueness among all physical H1 states. The added mass coefficient appears
explicitly in each physical equation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem intervalSobolevShiftedPointForm_ofEnergy (hlr : l < r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    {u v : ℝ → ℝ} (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r) :
    intervalSobolevShiftedPointForm hlr D κ z hz c (ofEnergy hu hlr) (ofEnergy hv hlr) =
      intervalPointForm D κ z l r u v + c * ∫ x in l..r, u x * v x := by
  rw [intervalSobolevShiftedPointForm_apply,
    intervalPointForm_congr D κ z hlr.le hz
      (representative_ofEnergy hu hlr) (representative_ofEnergy hv hlr)]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hlr.le
  intro x hx
  change (ofEnergy hu hlr).representative hlr x * (ofEnergy hv hlr).representative hlr x =
    u x * v x
  rw [representative_ofEnergy hu hlr (Ioo_subset_Icc_self hx),
    representative_ofEnergy hv hlr (Ioo_subset_Icc_self hx)]

theorem SignedIntervalPointProblem.shifted_weak_iff (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    (∀ v : IntervalSobolevSpace l r,
      P.shiftedForm (ofEnergy hu P.interval_pos) v = inner ℝ f v.state) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v +
        P.massShift * (∫ x in l..r, u x * v x) = ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv
    have he := h (ofEnergy hv P.interval_pos)
    change intervalSobolevShiftedPointForm P.interval_pos P.diffusivity P.strength P.site
      P.site_mem P.massShift (ofEnergy hu P.interval_pos) (ofEnergy hv P.interval_pos) =
        intervalSobolevL2Load l r f (ofEnergy hv P.interval_pos) at he
    rwa [intervalSobolevShiftedPointForm_ofEnergy, intervalSobolevL2Load_ofEnergy] at he
  · intro h v
    change intervalSobolevShiftedPointForm P.interval_pos P.diffusivity P.strength P.site
      P.site_mem P.massShift (ofEnergy hu P.interval_pos) v = intervalSobolevL2Load l r f v
    rw [intervalSobolevShiftedPointForm_apply, intervalSobolevL2Load_representative P.interval_pos,
      intervalPointForm_congr P.diffusivity P.strength P.site P.interval_pos.le P.site_mem
        (representative_ofEnergy hu P.interval_pos) (fun _ _ => rfl)]
    have hm : (∫ x in l..r, (ofEnergy hu P.interval_pos).representative P.interval_pos x *
        v.representative P.interval_pos x) =
        ∫ x in l..r, u x * v.representative P.interval_pos x := by
      apply intervalIntegral.integral_congr_Ioo_of_le P.interval_pos.le
      intro x hx
      change (ofEnergy hu P.interval_pos).representative P.interval_pos x *
        v.representative P.interval_pos x = u x * v.representative P.interval_pos x
      rw [representative_ofEnergy hu P.interval_pos (Ioo_subset_Icc_self hx)]
    rw [hm]
    exact h (v.representative P.interval_pos) (v.representative_spec P.interval_pos).1

theorem SignedIntervalPointProblem.shiftedInverse_eq_iff_weak (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    P.shiftedInverse f = (ofEnergy hu P.interval_pos).state ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v +
        P.massShift * (∫ x in l..r, u x * v x) = ∫ x in l..r, f x * v x) := by
  rw [← P.shifted_weak_iff f hu, ← P.shiftedSolution_eq_iff f (ofEnergy hu P.interval_pos)]
  constructor
  · intro h
    exact (ext_state h).symm
  · intro h
    rw [h, P.shiftedInverse_apply]

theorem SignedIntervalPointProblem.shiftedSolution_physical (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : ℝ → ℝ) (hv : IntervalEnergy v l r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.shiftedSolution f).representative P.interval_pos) v +
        P.massShift * (∫ x in l..r, (P.shiftedSolution f).representative P.interval_pos x * v x) =
          ∫ x in l..r, f x * v x := by
  have hu := ((P.shiftedSolution f).representative_spec P.interval_pos).1
  apply (P.shifted_weak_iff f hu).mp _ v hv
  rw [ofEnergy_representative]
  exact P.shiftedSolution_spec f

theorem SignedIntervalPointProblem.shifted_physical_unique (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (heu : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      intervalPointForm P.diffusivity P.strength P.site l r u w +
        P.massShift * (∫ x in l..r, u x * w x) = ∫ x in l..r, f x * w x)
    (hev : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      intervalPointForm P.diffusivity P.strength P.site l r v w +
        P.massShift * (∫ x in l..r, v x * w x) = ∫ x in l..r, f x * w x) :
    EqOn u v (Icc l r) := by
  have h1 := (P.shiftedSolution_eq_iff f (ofEnergy hu P.interval_pos)).mpr
    ((P.shifted_weak_iff f hu).mpr heu)
  have h2 := (P.shiftedSolution_eq_iff f (ofEnergy hv P.interval_pos)).mpr
    ((P.shifted_weak_iff f hv).mpr hev)
  have he : ofEnergy hu P.interval_pos = ofEnergy hv P.interval_pos := h1.trans h2.symm
  intro x hx
  calc
    u x = (ofEnergy hu P.interval_pos).representative P.interval_pos x :=
      (representative_ofEnergy hu P.interval_pos hx).symm
    _ = (ofEnergy hv P.interval_pos).representative P.interval_pos x := by rw [he]
    _ = v x := representative_ofEnergy hv P.interval_pos hx

end TimeTraps.Analysis
