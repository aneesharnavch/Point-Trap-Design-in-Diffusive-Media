module

public import TimeTraps.Analysis.GraphShiftedContactOperatorDomain

@[expose] public section

/-! The mass shift disappears from the final operator graph. The resulting
operator is characterized by the original weighted gradient/contact form
against every actual graph H1 test, including the case of zero reactions. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.operator_graph_weak_iff
    (P : GraphShiftedContactOperatorProblem V E) (x y : GraphL2Product P.geometry) :
    (x, y) ∈ P.operator.graph ↔ ∃ v : GraphSobolevSpace P.geometry,
      graphSobolevSpaceStateL P.geometry v = x ∧
        ∀ w : GraphSobolevSpace P.geometry,
          P.contactForm v w = inner ℝ y (graphSobolevSpaceStateL P.geometry w) := by
  rw [P.operator_graph_iff]
  constructor
  · intro he
    have hs : graphSobolevSpaceStateL P.geometry (P.operatorSolution (y + x)) = x := he
    refine ⟨P.operatorSolution (y + x), hs, ?_⟩
    intro w
    have hw := P.operatorSolution_spec (y + x) w
    rw [P.operatorForm_eq, hs, inner_add_left] at hw
    linarith
  · rintro ⟨v, hv, hw⟩
    have hs : v = P.operatorSolution (y + x) := by
      apply (P.operatorSolution_eq_iff (y + x) v).mpr
      intro w
      rw [P.operatorForm_eq, hv, hw w, inner_add_left]
      ring
    rw [P.operatorInverse_apply, ← hs]
    exact hv

theorem GraphShiftedContactOperatorProblem.contactWeak_iff
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy P.geometry U u) :
    (∀ v : GraphSobolevSpace P.geometry,
      P.contactForm (graphSobolevSpaceOfEnergy P.geometry hu) v = P.operatorLoad f v) ↔
    (∀ (W : V → ℝ) (w : E → ℝ → ℝ), GraphEnergy P.geometry W w →
      graphContactForm P.geometry P.strength U W u w =
        ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, (f e) x * w e x) := by
  constructor
  · intro h W w hw
    have he := h (graphSobolevSpaceOfEnergy P.geometry hw)
    rwa [P.contactForm_ofEnergy hu hw, P.operatorLoad_ofEnergy f hw] at he
  · intro h v
    have hv : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy v) = v :=
      graphSobolevSpaceOfEnergy_representative_eq P.geometry v
    rw [← hv, P.contactForm_ofEnergy hu (P.operatorRep_energy v),
      P.operatorLoad_ofEnergy f (P.operatorRep_energy v)]
    exact h (P.operatorNodes v) (P.operatorRep v) (P.operatorRep_energy v)

theorem GraphShiftedContactOperatorProblem.operator_graph_physical_iff
    (P : GraphShiftedContactOperatorProblem V E) (x y : GraphL2Product P.geometry) :
    (x, y) ∈ P.operator.graph ↔ ∃ (U : V → ℝ) (u : E → ℝ → ℝ)
      (hu : GraphEnergy P.geometry U u),
      graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu) = x ∧
        ∀ (W : V → ℝ) (w : E → ℝ → ℝ), GraphEnergy P.geometry W w →
          graphContactForm P.geometry P.strength U W u w =
            ∑ e, ∫ z in (0 : ℝ)..P.geometry.length e, (y e) z * w e z := by
  rw [P.operator_graph_weak_iff]
  constructor
  · rintro ⟨v, hv, hw⟩
    have he : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy v) = v :=
      graphSobolevSpaceOfEnergy_representative_eq P.geometry v
    refine ⟨P.operatorNodes v, P.operatorRep v, P.operatorRep_energy v, ?_, ?_⟩
    · simpa only [he] using hv
    · apply (P.contactWeak_iff y (P.operatorRep_energy v)).mp
      intro w
      rw [he, P.operatorLoad_apply]
      exact hw w
  · rintro ⟨U, u, hu, hx, hw⟩
    refine ⟨graphSobolevSpaceOfEnergy P.geometry hu, hx, ?_⟩
    have he := (P.contactWeak_iff y hu).mpr hw
    intro w
    simpa only [P.operatorLoad_apply] using he w

end TimeTraps.Analysis
