module

public import TimeTraps.Analysis.RegularSturmData
public import TimeTraps.Analysis.IntervalContinuousMultiplierPairing

@[expose] public section

/-! The original regular Sturm form with conductance p, potential q and
real contacts, restricted to the independently defined selected-endpoint
H1 space. Its physical pairing retains the full coefficient functions. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def regularSturmPhysicalForm (p q : ℝ → ℝ) (κ z : ι → ℝ)
    (l r : ℝ) (u v : ℝ → ℝ) : ℝ :=
  (∫ x in l..r, p x * deriv u x * deriv v x) +
    (∫ x in l..r, q x * u x * v x) + ∑ i, κ i * u (z i) * v (z i)

noncomputable def RegularSturmProblem.fullForm (P : RegularSturmProblem ι l r) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  let gradient : IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp
      ((intervalContinuousMultiplyL P.conductance P.conductance_continuous).comp (gradientL l r))
      (gradientL l r)
  let potential : IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp
      ((intervalContinuousMultiplyL P.potential P.potential_continuous).comp (IntervalSobolevSpace.stateL l r))
      (IntervalSobolevSpace.stateL l r)
  gradient + potential +
    ∑ i, P.strength i • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (evalL P.boundary.interval_pos (P.site i) (P.site_mem i))
      (evalL P.boundary.interval_pos (P.site i) (P.site_mem i))

noncomputable def RegularSturmProblem.form (P : RegularSturmProblem ι l r) :
    IntervalSeparatedSpace P.boundary →L[ℝ] IntervalSeparatedSpace P.boundary →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalSeparatedSpace P.boundary) :=
    Submodule.seminormedAddCommGroup P.boundary.subspace
  letI : NormedSpace ℝ (IntervalSeparatedSpace P.boundary) :=
    Submodule.normedSpace P.boundary.subspace
  let i : IntervalSeparatedSpace P.boundary →L[ℝ] IntervalSobolevSpace l r :=
    P.boundary.subspace.subtypeL
  exact P.fullForm.bilinearComp i i

theorem RegularSturmProblem.fullForm_apply (P : RegularSturmProblem ι l r)
    (u v : IntervalSobolevSpace l r) :
    P.fullForm u v = regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r
      (u.representative P.boundary.interval_pos) (v.representative P.boundary.interval_pos) := by
  simp only [RegularSturmProblem.fullForm, add_apply, smul_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.mul_apply', evalL_apply, smul_eq_mul]
  change inner ℝ (intervalContinuousMultiplyL P.conductance P.conductance_continuous u.gradient)
    v.gradient + inner ℝ (intervalContinuousMultiplyL P.potential P.potential_continuous u.state)
    v.state + ∑ i, P.strength i *
      (u.representative P.boundary.interval_pos (P.site i) *
        v.representative P.boundary.interval_pos (P.site i)) = _
  rw [intervalContinuousMultiplyL_gradient_inner P.boundary.interval_pos,
    intervalContinuousMultiplyL_state_inner P.boundary.interval_pos]
  simp only [regularSturmPhysicalForm, mul_assoc]

theorem RegularSturmProblem.form_apply (P : RegularSturmProblem ι l r)
    (u v : IntervalSeparatedSpace P.boundary) :
    P.form u v = regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r
      (u.val.representative P.boundary.interval_pos) (v.val.representative P.boundary.interval_pos) :=
  P.fullForm_apply u.val v.val

theorem RegularSturmProblem.fullForm_symmetric (P : RegularSturmProblem ι l r)
    (u v : IntervalSobolevSpace l r) : P.fullForm u v = P.fullForm v u := by
  rw [P.fullForm_apply, P.fullForm_apply]
  unfold regularSturmPhysicalForm
  have hg : (fun x => P.conductance x * deriv (u.representative P.boundary.interval_pos) x *
      deriv (v.representative P.boundary.interval_pos) x) =
      (fun x => P.conductance x * deriv (v.representative P.boundary.interval_pos) x *
        deriv (u.representative P.boundary.interval_pos) x) := by funext x; ring
  have hp : (fun x => P.potential x * u.representative P.boundary.interval_pos x *
      v.representative P.boundary.interval_pos x) =
      (fun x => P.potential x * v.representative P.boundary.interval_pos x *
        u.representative P.boundary.interval_pos x) := by funext x; ring
  rw [hg, hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem RegularSturmProblem.form_symmetric (P : RegularSturmProblem ι l r)
    (u v : IntervalSeparatedSpace P.boundary) : P.form u v = P.form v u :=
  P.fullForm_symmetric u.val v.val

end TimeTraps.Analysis
