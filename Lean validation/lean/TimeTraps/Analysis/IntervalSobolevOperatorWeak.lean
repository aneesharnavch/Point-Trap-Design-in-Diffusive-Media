module

public import TimeTraps.Analysis.IntervalSobolevOperatorPositive
public import TimeTraps.Analysis.IntervalSobolevLaxMilgram

@[expose] public section

/-! Exact correspondence between the L2 inverse and the physical
variational problem with every signed AC/L2 test. L2 representatives of
forcing are used only under the integral; endpoint values are not assigned. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι]

theorem unitSobolevL2Load_representative (f : UnitIntervalL2) (v : UnitIntervalSobolev) :
    unitSobolevL2Load f v = ∫ x in (0 : ℝ)..1, f x * v.representative zero_lt_one x := by
  rw [unitSobolevL2Load_apply, L2.inner_def, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(v.representative_spec zero_lt_one).2.1] with x hx
  simp only [Real.inner_apply, hx]

theorem unitSobolevL2Load_ofEnergy (f : UnitIntervalL2)
    {v : ℝ → ℝ} (hv : IntervalEnergy v 0 1) :
    unitSobolevL2Load f (ofEnergy hv zero_lt_one) = ∫ x in (0 : ℝ)..1, f x * v x := by
  rw [unitSobolevL2Load_apply, L2.inner_def, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(ofEnergy_spec hv zero_lt_one).1] with x hx
  simp only [Real.inner_apply, hx]

theorem UnitPointProblem.solution_eq_iff (P : UnitPointProblem ι)
    (f : UnitIntervalL2) (u : UnitIntervalSobolev) :
    u = P.solution f ↔ ∀ v : UnitIntervalSobolev, P.form u v = inner ℝ f v.state := by
  constructor
  · rintro rfl
    exact P.solution_spec f
  · intro h
    apply P.form_coercive.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [P.form_coercive.continuousLinearEquivOfBilin_apply,
      P.form_coercive.continuousLinearEquivOfBilin_apply, h, P.solution_spec]

theorem UnitPointProblem.weak_iff (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) :
    (∀ v : UnitIntervalSobolev,
      P.form (ofEnergy hu zero_lt_one) v = inner ℝ f v.state) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
      unitPointForm P.diffusivity P.strength P.site u v = ∫ x in (0 : ℝ)..1, f x * v x) := by
  constructor
  · intro h v hv
    have he := h (ofEnergy hv zero_lt_one)
    change unitSobolevForm P.diffusivity P.strength P.site P.site_mem
      (ofEnergy hu zero_lt_one) (ofEnergy hv zero_lt_one) =
      unitSobolevL2Load f (ofEnergy hv zero_lt_one) at he
    rwa [unitSobolevForm_ofEnergy, unitSobolevL2Load_ofEnergy] at he
  · intro h v
    change unitSobolevForm P.diffusivity P.strength P.site P.site_mem
      (ofEnergy hu zero_lt_one) v = unitSobolevL2Load f v
    rw [unitSobolevForm_apply, unitSobolevL2Load_representative]
    rw [unitPointForm_congr P.diffusivity P.strength P.site P.site_mem
      (representative_ofEnergy hu zero_lt_one) (fun _ _ => rfl)]
    exact h (v.representative zero_lt_one) (v.representative_spec zero_lt_one).1

theorem UnitPointProblem.inverse_eq_iff_weak (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) :
    P.inverse f = (ofEnergy hu zero_lt_one).state ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
      unitPointForm P.diffusivity P.strength P.site u v = ∫ x in (0 : ℝ)..1, f x * v x) := by
  rw [← P.weak_iff f hu, ← P.solution_eq_iff f (ofEnergy hu zero_lt_one)]
  constructor
  · intro h
    exact (ext_state h).symm
  · intro h
    rw [h, P.inverse_apply]

theorem UnitPointProblem.solution_physical (P : UnitPointProblem ι)
    (f : UnitIntervalL2) (v : ℝ → ℝ) (hv : IntervalEnergy v 0 1) :
    unitPointForm P.diffusivity P.strength P.site
      ((P.solution f).representative zero_lt_one) v = ∫ x in (0 : ℝ)..1, f x * v x := by
  have hu := ((P.solution f).representative_spec zero_lt_one).1
  apply (P.weak_iff f hu).mp _ v hv
  rw [ofEnergy_representative]
  exact P.solution_spec f

end TimeTraps.Analysis
