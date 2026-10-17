module

public import TimeTraps.Analysis.RegularSturmForm

@[expose] public section

/-! A derived positive mass shift makes the full variable-coefficient
form coercive. The shift absorbs the arbitrary real potential and finite
signed contacts, using compact-interval lower bounds for p and w. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def RegularSturmProblem.massShift (P : RegularSturmProblem ι l r) : ℝ :=
  (intervalPointNegativeBound P.conductanceLower P.strength l r +
    ‖intervalContinuousCoefficient P.potential P.potential_continuous‖ + 1) / P.speedLower

theorem RegularSturmProblem.massShift_pos (P : RegularSturmProblem ι l r) : 0 < P.massShift := by
  have h := intervalPointNegativeBound_nonneg P.conductanceLower_pos P.boundary.interval_pos P.strength
  have hn := norm_nonneg (intervalContinuousCoefficient P.potential P.potential_continuous)
  exact div_pos (by linarith) P.speedLower_pos

noncomputable def RegularSturmProblem.shiftedForm (P : RegularSturmProblem ι l r) :
    IntervalSeparatedSpace P.boundary →L[ℝ] IntervalSeparatedSpace P.boundary →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalSeparatedSpace P.boundary) :=
    Submodule.seminormedAddCommGroup P.boundary.subspace
  letI : NormedSpace ℝ (IntervalSeparatedSpace P.boundary) :=
    Submodule.normedSpace P.boundary.subspace
  let mass : IntervalSeparatedSpace P.boundary →L[ℝ] IntervalSeparatedSpace P.boundary →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp P.stateL P.stateL
  exact P.form + P.massShift • mass

theorem RegularSturmProblem.fullForm_lower (P : RegularSturmProblem ι l r)
    (u : IntervalSobolevSpace l r) :
    intervalSobolevPointForm P.boundary.interval_pos P.conductanceLower P.strength P.site
      P.site_mem u u - ‖intervalContinuousCoefficient P.potential P.potential_continuous‖ *
        ‖u.state‖ ^ 2 ≤ P.fullForm u u := by
  have hp := intervalContinuousMultiplyL_lower P.conductance P.conductance_continuous
    P.conductanceLower P.conductanceLower_le u.gradient
  have hq := intervalContinuousMultiplyL_uniform_lower P.potential P.potential_continuous u.state
  simp only [intervalSobolevPointForm, intervalSobolevGradientForm,
    RegularSturmProblem.fullForm, add_apply, smul_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.mul_apply', evalL_apply, smul_eq_mul]
  change P.conductanceLower * inner ℝ u.gradient u.gradient +
      (∑ i, P.strength i * (u.representative P.boundary.interval_pos (P.site i) *
        u.representative P.boundary.interval_pos (P.site i))) -
      ‖intervalContinuousCoefficient P.potential P.potential_continuous‖ * ‖u.state‖ ^ 2 ≤
    inner ℝ (intervalContinuousMultiplyL P.conductance P.conductance_continuous u.gradient)
      u.gradient +
    inner ℝ (intervalContinuousMultiplyL P.potential P.potential_continuous u.state) u.state +
      ∑ i, P.strength i * (u.representative P.boundary.interval_pos (P.site i) *
        u.representative P.boundary.interval_pos (P.site i))
  rw [real_inner_self_eq_norm_sq]
  linarith

theorem RegularSturmProblem.shiftedForm_symmetric (P : RegularSturmProblem ι l r)
    (u v : IntervalSeparatedSpace P.boundary) : P.shiftedForm u v = P.shiftedForm v u := by
  change P.form u v + P.massShift * inner ℝ (P.stateL u) (P.stateL v) =
    P.form v u + P.massShift * inner ℝ (P.stateL v) (P.stateL u)
  rw [P.form_symmetric, real_inner_comm (P.stateL u) (P.stateL v)]

theorem RegularSturmProblem.shiftedForm_coercive (P : RegularSturmProblem ι l r) :
    @IsCoercive (IntervalSeparatedSpace P.boundary)
      (Submodule.seminormedAddCommGroup P.boundary.subspace)
      (Submodule.normedSpace P.boundary.subspace) P.shiftedForm := by
  obtain ⟨c, hc, hb⟩ := intervalSobolevShiftedPointForm_coercive P.boundary.interval_pos
    P.conductanceLower_pos P.strength P.site P.site_mem
  refine ⟨c, hc, ?_⟩
  intro u
  apply (hb u.val).trans
  have hf := P.fullForm_lower u.val
  have hm := intervalWeightedStateL_lower P.boundary.interval_pos P.speed P.speed_continuous
    (fun x hx => (P.speed_pos x hx).le) P.speedLower P.speedLower_le u.val
  change P.speedLower * ‖u.val.state‖ ^ 2 ≤ ‖P.stateL u‖ ^ 2 at hm
  have hh := mul_le_mul_of_nonneg_left hm P.massShift_pos.le
  have hs : P.massShift * P.speedLower =
      intervalPointNegativeBound P.conductanceLower P.strength l r +
        ‖intervalContinuousCoefficient P.potential P.potential_continuous‖ + 1 :=
    div_mul_cancel₀ _ P.speedLower_pos.ne'
  rw [← mul_assoc, hs] at hh
  change intervalSobolevPointForm P.boundary.interval_pos P.conductanceLower P.strength
      P.site P.site_mem u.val u.val +
      (intervalPointNegativeBound P.conductanceLower P.strength l r + 1) *
        inner ℝ u.val.state u.val.state ≤
    P.fullForm u.val u.val + P.massShift * inner ℝ (P.stateL u) (P.stateL u)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith

end TimeTraps.Analysis
