module

public import TimeTraps.Analysis.SignedIntervalPointPhysical
public import TimeTraps.Analysis.GeneralIntervalPointOperator

@[expose] public section

/-! The signed construction agrees exactly with the previously constructed
nonnegative-contact operator whenever those original hypotheses hold.
The auxiliary mass shift does not change the physical operator. -/

namespace TimeTraps.Analysis

variable {ι : Type*} [Fintype ι] {l r : ℝ}

def IntervalPointProblem.signedProblem (P : IntervalPointProblem ι l r) :
    SignedIntervalPointProblem ι l r where
  interval_pos := P.interval_pos
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := P.strength
  site := P.site
  site_mem := P.site_mem

theorem IntervalPointProblem.signedProblem_form (P : IntervalPointProblem ι l r) :
    P.signedProblem.form = P.form := rfl

theorem IntervalPointProblem.signedProblem_operator (P : IntervalPointProblem ι l r) :
    P.signedProblem.operator = P.operator := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [P.signedProblem.operator_graph_iff_hilbert, P.operator_graph_iff_hilbert,
    P.signedProblem_form]

end TimeTraps.Analysis
