module

public import TimeTraps.Analysis.GeneralIntervalPointPositive

@[expose] public section

/-! Exact correspondence of the arbitrary-interval solution operator with
the physical equation against every signed AC/L2 test function. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem intervalSobolevL2Load_representative (hlr : l < r)
    (f : IntervalSobolevL2 l r) (v : IntervalSobolevSpace l r) :
    intervalSobolevL2Load l r f v = ∫ x in l..r, f x * v.representative hlr x := by
  rw [intervalSobolevL2Load_apply, L2.inner_def, intervalIntegral.integral_of_le hlr.le,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(v.representative_spec hlr).2.1] with x hx
  simp only [Real.inner_apply, hx]

theorem intervalSobolevL2Load_ofEnergy (hlr : l < r) (f : IntervalSobolevL2 l r)
    {v : ℝ → ℝ} (hv : IntervalEnergy v l r) :
    intervalSobolevL2Load l r f (ofEnergy hv hlr) = ∫ x in l..r, f x * v x := by
  rw [intervalSobolevL2Load_apply, L2.inner_def, intervalIntegral.integral_of_le hlr.le,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(ofEnergy_spec hv hlr).1] with x hx
  simp only [Real.inner_apply, hx]

theorem intervalSobolevPointForm_ofEnergy (hlr : l < r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r)
    {u v : ℝ → ℝ} (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r) :
    intervalSobolevPointForm hlr D κ z hz (ofEnergy hu hlr) (ofEnergy hv hlr) =
      intervalPointForm D κ z l r u v := by
  rw [intervalSobolevPointForm_apply]
  exact intervalPointForm_congr D κ z hlr.le hz
    (representative_ofEnergy hu hlr) (representative_ofEnergy hv hlr)

theorem IntervalPointProblem.solution_eq_iff (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (u : IntervalSobolevSpace l r) :
    u = P.solution f ↔ ∀ v : IntervalSobolevSpace l r, P.form u v = inner ℝ f v.state := by
  constructor
  · rintro rfl
    exact P.solution_spec f
  · intro h
    apply P.form_coercive.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [P.form_coercive.continuousLinearEquivOfBilin_apply,
      P.form_coercive.continuousLinearEquivOfBilin_apply, h, P.solution_spec]

theorem IntervalPointProblem.weak_iff (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    (∀ v : IntervalSobolevSpace l r,
      P.form (ofEnergy hu P.interval_pos) v = inner ℝ f v.state) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv
    have he := h (ofEnergy hv P.interval_pos)
    change intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem
      (ofEnergy hu P.interval_pos) (ofEnergy hv P.interval_pos) =
      intervalSobolevL2Load l r f (ofEnergy hv P.interval_pos) at he
    rwa [intervalSobolevPointForm_ofEnergy, intervalSobolevL2Load_ofEnergy] at he
  · intro h v
    change intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem
      (ofEnergy hu P.interval_pos) v = intervalSobolevL2Load l r f v
    rw [intervalSobolevPointForm_apply, intervalSobolevL2Load_representative P.interval_pos]
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.interval_pos.le P.site_mem
      (representative_ofEnergy hu P.interval_pos) (fun _ _ => rfl)]
    exact h (v.representative P.interval_pos) (v.representative_spec P.interval_pos).1

theorem IntervalPointProblem.inverse_eq_iff_weak (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    P.inverse f = (ofEnergy hu P.interval_pos).state ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x) := by
  rw [← P.weak_iff f hu, ← P.solution_eq_iff f (ofEnergy hu P.interval_pos)]
  constructor
  · intro h
    exact (ext_state h).symm
  · intro h
    rw [h, P.inverse_apply]

theorem IntervalPointProblem.solution_physical (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : ℝ → ℝ) (hv : IntervalEnergy v l r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.solution f).representative P.interval_pos) v = ∫ x in l..r, f x * v x := by
  have hu := ((P.solution f).representative_spec P.interval_pos).1
  apply (P.weak_iff f hu).mp _ v hv
  rw [ofEnergy_representative]
  exact P.solution_spec f

end TimeTraps.Analysis
