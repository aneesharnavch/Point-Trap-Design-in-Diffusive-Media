module

public import TimeTraps.Analysis.RegularSturmVariationalNonnegative

@[expose] public section

/-! Absolute value stays in the actual separated-boundary H1 space,
preserving the original weighted mass and signed variable-coefficient form. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def IntervalSeparatedBoundary.absState (B : IntervalSeparatedBoundary l r)
    (u : IntervalSeparatedSpace B) : IntervalSeparatedSpace B :=
  B.ofEnergy (u.val.representative_spec B.interval_pos).1.abs
    (fun x hx => by rw [B.representative_zero u hx, abs_zero])

theorem IntervalSeparatedBoundary.absState_representative (B : IntervalSeparatedBoundary l r)
    (u : IntervalSeparatedSpace B) :
    EqOn ((B.absState u).val.representative B.interval_pos)
      (fun x => |u.val.representative B.interval_pos x|) (Icc l r) :=
  B.ofEnergy_representative _ _

theorem RegularSturmProblem.absState_mass (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    ‖P.stateL (P.boundary.absState u)‖ ^ 2 = ‖P.stateL u‖ ^ 2 := by
  rw [← P.squareMass_representative, ← P.squareMass_representative,
    P.squareMass_congr (P.boundary.absState_representative u), P.squareMass_abs]

theorem RegularSturmProblem.absState_form (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    P.form (P.boundary.absState u) (P.boundary.absState u) = P.form u u := by
  rw [P.form_apply, P.form_apply]
  rw [regularSturmPhysicalForm_congr P.conductance P.potential P.strength P.site
    P.boundary.interval_pos.le P.site_mem
    (P.boundary.absState_representative u) (P.boundary.absState_representative u)]
  exact P.quadraticForm_abs (u.val.representative_spec P.boundary.interval_pos).1

end TimeTraps.Analysis
