module

public import TimeTraps.Analysis.IntervalPointFormHilbert
public import TimeTraps.Analysis.LaxMilgramOperator
public import TimeTraps.Analysis.IntervalSobolevCompactL2
public import TimeTraps.Analysis.IntervalSobolevDense

@[expose] public section

/-! Actual L2 solution operators on an arbitrary nondegenerate finite
interval. Endpoints and physical length remain parameters of the independent
H1 and L2 spaces; the model is not defined by an assumed unit normalization. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

structure IntervalPointProblem (ι : Type*) [Fintype ι] (l r : ℝ) where
  interval_pos : l < r
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : ι → ℝ
  strength_nonneg : ∀ i, 0 ≤ strength i
  site : ι → ℝ
  site_mem : ∀ i, site i ∈ Icc l r
  positive_contact : ∃ i, 0 < strength i

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def IntervalPointProblem.form (P : IntervalPointProblem ι l r) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem

theorem IntervalPointProblem.form_coercive (P : IntervalPointProblem ι l r) :
    IsCoercive P.form := by
  obtain ⟨k, hk⟩ := P.positive_contact
  exact intervalSobolevPointForm_coercive P.interval_pos P.diffusivity_pos
    P.strength P.site P.strength_nonneg P.site_mem k hk

def IntervalPointProblem.solution (P : IntervalPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevSpace l r :=
  (coerciveFormSolutionL P.form P.form_coercive).comp (intervalSobolevL2Load l r)

def IntervalPointProblem.inverse (P : IntervalPointProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  (stateL l r).comp P.solution

theorem IntervalPointProblem.solution_spec (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalSobolevSpace l r) :
    P.form (P.solution f) v = inner ℝ f v.state :=
  coerciveFormSolutionL_spec P.form P.form_coercive (intervalSobolevL2Load l r f) v

theorem IntervalPointProblem.inverse_apply (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : P.inverse f = (P.solution f).state := rfl

theorem IntervalPointProblem.inverse_compact (P : IntervalPointProblem ι l r) :
    IsCompactOperator P.inverse := (stateL_isCompact P.interval_pos).comp_clm P.solution

theorem IntervalPointProblem.form_symmetric (P : IntervalPointProblem ι l r)
    (u v : IntervalSobolevSpace l r) : P.form u v = P.form v u :=
  intervalSobolevPointForm_symmetric P.interval_pos P.diffusivity P.strength P.site P.site_mem u v

end

end TimeTraps.Analysis
