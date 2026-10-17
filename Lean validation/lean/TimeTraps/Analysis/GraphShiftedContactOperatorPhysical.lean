module

public import TimeTraps.Analysis.GraphShiftedContactOperatorForm

@[expose] public section

/-! The shifted bounded form equals the original mass, conductance and
vertex contact integrals for every full graph H1 test. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] [Fintype E] in
theorem GraphShiftedContactOperatorProblem.operatorNodes_ofEnergy
    (P : GraphShiftedContactOperatorProblem V E) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) :
    P.operatorNodes (graphSobolevSpaceOfEnergy P.geometry hu) = U := by
  funext v
  exact graphSobolevSpaceOfEnergy_node P.geometry hu v

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.operatorRep_ofEnergy
    (P : GraphShiftedContactOperatorProblem V E) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) (e : E) :
    EqOn (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hu) e) (u e)
      (Icc 0 (P.geometry.length e)) := graphSobolevSpaceOfEnergy_representative P.geometry hu e

theorem GraphShiftedContactOperatorProblem.operatorForm_ofEnergy
    (P : GraphShiftedContactOperatorProblem V E) {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) (hw : GraphEnergy P.geometry W w) :
    P.operatorForm (graphSobolevSpaceOfEnergy P.geometry hu) (graphSobolevSpaceOfEnergy P.geometry hw) =
      graphShiftedContactForm P.geometry P.strength U W u w := by
  rw [P.operatorForm_apply, P.operatorNodes_ofEnergy hu, P.operatorNodes_ofEnergy hw]
  unfold graphShiftedContactForm graphContactForm
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr_Ioo_of_le (P.geometry.length_pos e).le
    intro x hx
    change P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hu) e x *
      P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hw) e x = u e x * w e x
    rw [P.operatorRep_ofEnergy hu e (Ioo_subset_Icc_self hx),
      P.operatorRep_ofEnergy hw e (Ioo_subset_Icc_self hx)]
  · congr 1
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr_Ioo_of_le (P.geometry.length_pos e).le
    intro x hx
    change P.geometry.conductance e x *
      deriv (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hu) e) x *
      deriv (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hw) e) x =
        P.geometry.conductance e x * deriv (u e) x * deriv (w e) x
    rw [((P.operatorRep_ofEnergy hu e).mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx,
      ((P.operatorRep_ofEnergy hw e).mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx]

theorem GraphShiftedContactOperatorProblem.contactForm_ofEnergy
    (P : GraphShiftedContactOperatorProblem V E) {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) (hw : GraphEnergy P.geometry W w) :
    P.contactForm (graphSobolevSpaceOfEnergy P.geometry hu) (graphSobolevSpaceOfEnergy P.geometry hw) =
      graphContactForm P.geometry P.strength U W u w := by
  rw [P.contactForm_apply, P.operatorNodes_ofEnergy hu, P.operatorNodes_ofEnergy hw]
  unfold graphContactForm
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_Ioo_of_le (P.geometry.length_pos e).le
  intro x hx
  change P.geometry.conductance e x *
    deriv (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hu) e) x *
    deriv (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hw) e) x =
      P.geometry.conductance e x * deriv (u e) x * deriv (w e) x
  rw [((P.operatorRep_ofEnergy hu e).mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx,
    ((P.operatorRep_ofEnergy hw e).mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx]

end TimeTraps.Analysis
