module

public import TimeTraps.Analysis.SignedIntervalPointWeak
public import TimeTraps.Analysis.IntervalEnergyAbsolute

@[expose] public section

/-! Absolute value of an actual H1 representative remains in the same
Hilbert space and preserves the shifted quadratic form, even when contact
strengths are negative. Nonnegative L2 forcing pairs nonpositively with
the difference between a state and its absolute value. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedIntervalPointProblem.orderAbs (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) : IntervalSobolevSpace l r :=
  ofEnergy ((u.representative_spec P.interval_pos).1.abs) P.interval_pos

theorem SignedIntervalPointProblem.orderAbs_state_ae (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) :
    (P.orderAbs u).state =ᵐ[volume.restrict (Ioo l r)] fun x => |u.representative P.interval_pos x| :=
  (ofEnergy_spec ((u.representative_spec P.interval_pos).1.abs) P.interval_pos).1

theorem SignedIntervalPointProblem.orderAbs_representative (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) :
    EqOn ((P.orderAbs u).representative P.interval_pos)
      (fun x => |u.representative P.interval_pos x|) (Icc l r) :=
  representative_ofEnergy ((u.representative_spec P.interval_pos).1.abs) P.interval_pos

theorem SignedIntervalPointProblem.shiftedForm_orderAbs (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) :
    P.shiftedForm (P.orderAbs u) (P.orderAbs u) = P.shiftedForm u u := by
  change intervalSobolevShiftedPointForm P.interval_pos P.diffusivity P.strength P.site
    P.site_mem P.massShift
      (ofEnergy ((u.representative_spec P.interval_pos).1.abs) P.interval_pos)
      (ofEnergy ((u.representative_spec P.interval_pos).1.abs) P.interval_pos) =
    intervalSobolevShiftedPointForm P.interval_pos P.diffusivity P.strength P.site
      P.site_mem P.massShift u u
  rw [intervalSobolevShiftedPointForm_ofEnergy, intervalSobolevShiftedPointForm_apply,
    (u.representative_spec P.interval_pos).1.abs_point_form]
  simp only [← pow_two, sq_abs]

theorem SignedIntervalPointProblem.orderAbs_load_nonpos (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (hf : ∀ᵐ x ∂volume.restrict (Ioo l r), 0 ≤ f x)
    (u : IntervalSobolevSpace l r) :
    inner ℝ f (u - P.orderAbs u).state ≤ 0 := by
  have hs : (u - P.orderAbs u).state = u.state - (P.orderAbs u).state :=
    (stateL l r).map_sub u (P.orderAbs u)
  rw [hs, L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [hf, Lp.coeFn_sub u.state (P.orderAbs u).state,
    (u.representative_spec P.interval_pos).2.1, P.orderAbs_state_ae u] with x hfx hx hu hv
  simp only [Real.inner_apply, hx, Pi.sub_apply, hu, hv]
  exact mul_nonpos_of_nonneg_of_nonpos hfx (sub_nonpos.mpr (le_abs_self _))

end TimeTraps.Analysis
