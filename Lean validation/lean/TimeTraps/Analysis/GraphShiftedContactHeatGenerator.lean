module

public import TimeTraps.Analysis.GraphShiftedContactHeatSemigroup

@[expose] public section

/-! The full strong generator of the evolution with its mass shift removed
is exactly the original graph contact operator. Both directions use the
actual inverse domain, rather than a smaller family of smooth test states. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatCurve_zero
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry) :
    P.heatCurve x 0 = x := by
  simp only [heatCurve, Real.exp_zero, P.operatorCompactPositiveInverse.heatCurve_zero, one_smul]

theorem GraphShiftedContactOperatorProblem.heatCurve_shift_derivative_iff
    (P : GraphShiftedContactOperatorProblem V E) (x v : GraphL2Product P.geometry) :
    HasDerivWithinAt (P.heatCurve x) v (Ici 0) 0 ↔
      HasDerivWithinAt (P.operatorCompactPositiveInverse.heatCurve x) (v - x) (Ici 0) 0 := by
  have hp : HasDerivWithinAt Real.exp 1 (Ici 0) 0 := by
    simpa only [Real.exp_zero] using (Real.hasDerivAt_exp 0).hasDerivWithinAt
  have hn : HasDerivWithinAt (fun t : ℝ => Real.exp (-t)) (-1) (Ici 0) 0 := by
    have hid : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id _).neg
    simpa using hid.exp.hasDerivWithinAt
  constructor
  · intro hv
    have hd := hn.smul hv
    have he : (fun t : ℝ => Real.exp (-t) • P.heatCurve x t) =
        P.operatorCompactPositiveInverse.heatCurve x := by
      funext t
      rw [heatCurve, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
    change HasDerivWithinAt (fun t : ℝ => Real.exp (-t) • P.heatCurve x t)
      (Real.exp (-0) • v + (-1) • P.heatCurve x 0) (Ici 0) 0 at hd
    rw [he] at hd
    simpa only [P.heatCurve_zero, neg_one_smul, neg_zero, Real.exp_zero, one_smul,
      ← sub_eq_add_neg] using hd
  · intro hv
    have hd := hp.smul hv
    change HasDerivWithinAt (P.heatCurve x)
      (Real.exp 0 • (v - x) + 1 • P.operatorCompactPositiveInverse.heatCurve x 0) (Ici 0) 0 at hd
    simpa only [P.operatorCompactPositiveInverse.heatCurve_zero, one_smul, Real.exp_zero,
      sub_add_cancel] using hd

theorem GraphShiftedContactOperatorProblem.heatCurve_generator_iff
    (P : GraphShiftedContactOperatorProblem V E) (x v : GraphL2Product P.geometry) :
    HasDerivWithinAt (P.heatCurve x) v (Ici 0) 0 ↔ (x, -v) ∈ P.operator.graph := by
  rw [P.heatCurve_shift_derivative_iff,
    P.operatorCompactPositiveInverse.heatCurve_generator_iff, P.operator_graph_iff]
  constructor
  · rintro ⟨hx, hv⟩
    have he : -v + x = inverseOperator P.operatorInverse P.operatorInverse_injective ⟨x, hx⟩ := by
      have hh := congrArg Neg.neg hv
      rw [neg_sub, neg_neg] at hh
      calc
        -v + x = x - v := by abel
        _ = _ := hh
    rw [he]
    exact inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective ⟨x, hx⟩
  · intro he
    have hx : x ∈ (inverseOperator P.operatorInverse P.operatorInverse_injective).domain := ⟨-v + x, he⟩
    refine ⟨hx, ?_⟩
    have hh : inverseOperator P.operatorInverse P.operatorInverse_injective ⟨x, hx⟩ = -v + x := by
      apply P.operatorInverse_injective
      exact (inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective ⟨x, hx⟩).trans he.symm
    rw [hh]
    abel

theorem GraphShiftedContactOperatorProblem.heatCurve_generator_physical_iff
    (P : GraphShiftedContactOperatorProblem V E) (x v : GraphL2Product P.geometry) :
    HasDerivWithinAt (P.heatCurve x) v (Ici 0) 0 ↔
      ∃ (U : V → ℝ) (u : E → ℝ → ℝ) (hu : TimeTraps.Graph.GraphEnergy P.geometry U u),
        graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu) = x ∧
          ∀ (W : V → ℝ) (w : E → ℝ → ℝ), TimeTraps.Graph.GraphEnergy P.geometry W w →
            graphContactForm P.geometry P.strength U W u w =
              ∑ e, ∫ z in (0 : ℝ)..P.geometry.length e, ((-v) e) z * w e z := by
  rw [P.heatCurve_generator_iff, P.operator_graph_physical_iff]

end TimeTraps.Analysis
