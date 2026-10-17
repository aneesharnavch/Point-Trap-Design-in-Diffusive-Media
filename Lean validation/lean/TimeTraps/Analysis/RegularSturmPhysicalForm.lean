module

public import TimeTraps.Analysis.RegularSturmOperator

@[expose] public section

/-! Exact physical state, load and form identities for the regular
Sturm operator. The Hilbert coordinate is sqrt(w) times the physical
state, so a general Hilbert load f acts physically as sqrt(w) f. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem regularSturmPhysicalForm_congr (p q : ℝ → ℝ) (κ z : ι → ℝ)
    (hlr : l ≤ r) (hz : ∀ i, z i ∈ Icc l r) {u v U V : ℝ → ℝ}
    (hu : EqOn u U (Icc l r)) (hv : EqOn v V (Icc l r)) :
    regularSturmPhysicalForm p q κ z l r u v = regularSturmPhysicalForm p q κ z l r U V := by
  unfold regularSturmPhysicalForm
  congr 1
  · congr 1
    · apply intervalIntegral.integral_congr_Ioo_of_le hlr
      intro x hx
      change p x * deriv u x * deriv v x = p x * deriv U x * deriv V x
      rw [(hu.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx,
        (hv.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx]
    · apply intervalIntegral.integral_congr_Ioo_of_le hlr
      intro x hx
      change q x * u x * v x = q x * U x * V x
      rw [hu (Ioo_subset_Icc_self hx), hv (Ioo_subset_Icc_self hx)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [hu (hz i), hv (hz i)]

theorem RegularSturmProblem.form_ofEnergy (P : RegularSturmProblem ι l r)
    {u v : ℝ → ℝ} (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0) :
    P.form (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hv hvz) =
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v := by
  rw [P.form_apply]
  exact regularSturmPhysicalForm_congr _ _ _ _ P.boundary.interval_pos.le P.site_mem
    (P.boundary.ofEnergy_representative hu huz) (P.boundary.ofEnergy_representative hv hvz)

theorem RegularSturmProblem.stateL_representative_ae (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    P.stateL u =ᵐ[volume.restrict (Ioo l r)]
      (fun x => Real.sqrt (P.speed x) * u.val.representative P.boundary.interval_pos x) := by
  have h := intervalWeightedStateL_coe P.speed P.speed_continuous u.val
  change P.stateL u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * u.val.state x) at h
  filter_upwards [h, (u.val.representative_spec P.boundary.interval_pos).2.1] with x hx hu
  rw [hx, hu]

theorem RegularSturmProblem.stateL_ofEnergy_ae (P : RegularSturmProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    P.stateL (P.boundary.ofEnergy hu huz) =ᵐ[volume.restrict (Ioo l r)]
      (fun x => Real.sqrt (P.speed x) * u x) := by
  filter_upwards [P.stateL_representative_ae (P.boundary.ofEnergy hu huz),
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx hmem
  rw [hx, P.boundary.ofEnergy_representative hu huz (Ioo_subset_Icc_self hmem)]

theorem RegularSturmProblem.load_representative (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalSeparatedSpace P.boundary) :
    P.load f v = ∫ x in l..r, f x * Real.sqrt (P.speed x) * v.val.representative P.boundary.interval_pos x := by
  rw [P.load_apply, L2.inner_def, intervalIntegral.integral_of_le P.boundary.interval_pos.le,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [P.stateL_representative_ae v] with x hx
  simp only [Real.inner_apply, hx, mul_assoc]

theorem RegularSturmProblem.load_ofEnergy (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {v : ℝ → ℝ} (hv : IntervalEnergy v l r)
    (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0) :
    P.load f (P.boundary.ofEnergy hv hvz) = ∫ x in l..r, f x * Real.sqrt (P.speed x) * v x := by
  rw [P.load_representative]
  apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
  intro x hx
  change f x * Real.sqrt (P.speed x) *
    (P.boundary.ofEnergy hv hvz).val.representative P.boundary.interval_pos x = _
  rw [P.boundary.ofEnergy_representative hv hvz (Ioo_subset_Icc_self hx)]

end TimeTraps.Analysis
