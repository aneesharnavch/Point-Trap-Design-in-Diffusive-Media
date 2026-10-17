module

public import TimeTraps.Analysis.GraphShiftedContactOrderAbsoluteData

@[expose] public section

/-! Taking the actual graph absolute value preserves both the original
weighted contact quadratic form and its coercive ordinary-mass shift. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.contactForm_orderAbs (P : GraphShiftedContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) :
    P.contactForm (P.operatorOrderAbs u) (P.operatorOrderAbs u) = P.contactForm u u := by
  change P.contactForm
    (graphSobolevSpaceOfEnergy P.geometry (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)))
    (graphSobolevSpaceOfEnergy P.geometry (graphContactEnergy_abs P.geometry (P.operatorRep_energy u))) = _
  rw [P.contactForm_ofEnergy, P.contactForm_apply]
  unfold graphContactForm
  simp only [mul_assoc, ← pow_two, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [((P.operatorRep_energy u).edge_energy e).abs_derivative_square_ae]
    with x hx
  change P.geometry.conductance e x * deriv (fun y => |P.operatorRep u e y|) x ^ 2 =
    P.geometry.conductance e x * deriv (P.operatorRep u e) x ^ 2
  rw [hx]

theorem GraphShiftedContactOperatorProblem.operatorForm_orderAbs
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) :
    P.operatorForm (P.operatorOrderAbs u) (P.operatorOrderAbs u) = P.operatorForm u u := by
  rw [P.operatorForm_eq, P.operatorForm_eq, P.operatorOrderAbs_mass, P.contactForm_orderAbs]

end TimeTraps.Analysis
