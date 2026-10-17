module

public import TimeTraps.Analysis.SignedPeriodicPointPhysical
public import TimeTraps.Analysis.IntervalPeriodicOperator

@[expose] public section

/-! The signed construction agrees exactly with the previously constructed
nonnegative-contact periodic operator whenever those original hypotheses hold.
The auxiliary mass shift does not change the physical operator. -/

namespace TimeTraps.Analysis

variable {ι : Type*} [Fintype ι] {l r : ℝ}

def PeriodicPointProblem.signedProblem (P : PeriodicPointProblem ι l r) :
    SignedPeriodicPointProblem ι l r where
  boundary := P.boundary
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := P.strength
  site := P.site
  site_mem := P.site_mem

theorem PeriodicPointProblem.signedProblem_form (P : PeriodicPointProblem ι l r) :
    P.signedProblem.form = P.form := rfl

theorem PeriodicPointProblem.signedProblem_operator (P : PeriodicPointProblem ι l r) :
    P.signedProblem.operator = P.operator := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [P.signedProblem.operator_graph_iff_hilbert, P.operator_graph_iff_hilbert,
    P.signedProblem_form]

end TimeTraps.Analysis
