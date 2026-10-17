module

public import TimeTraps.Analysis.LaxMilgramOperator
public import TimeTraps.Analysis.IntervalSobolevForm
public import TimeTraps.Analysis.IntervalSobolevCompactL2
public import TimeTraps.Analysis.IntervalSobolevDense

@[expose] public section

/-! The actual L2-to-H1 and L2-to-L2 solution operators for the unit
interval with diffusivity D>0 and finitely many nonnegative point contacts,
at least one of positive strength. Sites may include either endpoint.
All forcing terms are arbitrary L2 functions; the test space is full H1. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace
open scoped BigOperators

noncomputable section

abbrev UnitIntervalL2 := IntervalSobolevL2 (0 : ℝ) 1

structure UnitPointProblem (ι : Type*) [Fintype ι] where
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : ι → ℝ
  strength_nonneg : ∀ i, 0 ≤ strength i
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc (0 : ℝ) 1
  positive_contact : ∃ i, 0 < strength i

def unitSobolevL2Load : UnitIntervalL2 →L[ℝ] UnitIntervalSobolev →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ UnitIntervalL2) (stateL 0 1)

theorem unitSobolevL2Load_apply (f : UnitIntervalL2) (v : UnitIntervalSobolev) :
    unitSobolevL2Load f v = inner ℝ f v.state := rfl

def UnitPointProblem.form {ι : Type*} [Fintype ι] (P : UnitPointProblem ι) :=
  unitSobolevForm P.diffusivity P.strength P.site P.site_mem

theorem UnitPointProblem.form_coercive {ι : Type*} [Fintype ι]
    (P : UnitPointProblem ι) : IsCoercive P.form := by
  obtain ⟨k, hk⟩ := P.positive_contact
  exact unitSobolevForm_coercive P.diffusivity_pos P.strength P.site
    P.strength_nonneg P.site_mem k hk

def UnitPointProblem.solution {ι : Type*} [Fintype ι] (P : UnitPointProblem ι) :
    UnitIntervalL2 →L[ℝ] UnitIntervalSobolev :=
  (coerciveFormSolutionL P.form P.form_coercive).comp unitSobolevL2Load

def UnitPointProblem.inverse {ι : Type*} [Fintype ι] (P : UnitPointProblem ι) :
    UnitIntervalL2 →L[ℝ] UnitIntervalL2 :=
  (stateL 0 1).comp P.solution

theorem UnitPointProblem.solution_spec {ι : Type*} [Fintype ι]
    (P : UnitPointProblem ι) (f : UnitIntervalL2) (v : UnitIntervalSobolev) :
    P.form (P.solution f) v = inner ℝ f v.state :=
  coerciveFormSolutionL_spec P.form P.form_coercive (unitSobolevL2Load f) v

theorem UnitPointProblem.inverse_apply {ι : Type*} [Fintype ι]
    (P : UnitPointProblem ι) (f : UnitIntervalL2) :
    P.inverse f = (P.solution f).state := rfl

theorem UnitPointProblem.inverse_compact {ι : Type*} [Fintype ι]
    (P : UnitPointProblem ι) : IsCompactOperator P.inverse :=
  (stateL_isCompact zero_lt_one).comp_clm P.solution

theorem UnitPointProblem.form_symmetric {ι : Type*} [Fintype ι]
    (P : UnitPointProblem ι) (u v : UnitIntervalSobolev) : P.form u v = P.form v u := by
  simp only [UnitPointProblem.form, unitSobolevForm, unitSobolevGradientForm,
    add_apply, smul_apply, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  rw [real_inner_comm (gradientL 0 1 u) (gradientL 0 1 v)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (evalL zero_lt_one (P.site i) (P.site_mem i) u)]

end

end TimeTraps.Analysis
