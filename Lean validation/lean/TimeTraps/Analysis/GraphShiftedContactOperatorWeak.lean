module

public import TimeTraps.Analysis.GraphShiftedContactOperatorSolution
public import TimeTraps.Analysis.GraphShiftedContactOperatorPhysical

@[expose] public section

/-! Shifted physical existence and uniqueness for every edge L2 source, with all
original graph energy tests. Uniqueness means equal nodal values and equal
states on each closed physical edge; off-edge representatives are irrelevant. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

structure GraphShiftedContactL2WeakEquation (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry)
    (U : V → ℝ) (u : E → ℝ → ℝ) : Prop where
  energy : GraphEnergy P.geometry U u
  weak_form : ∀ (W : V → ℝ) (w : E → ℝ → ℝ), GraphEnergy P.geometry W w →
    graphShiftedContactForm P.geometry P.strength U W u w =
        ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, (f e) x * w e x

theorem GraphShiftedContactOperatorProblem.operatorWeak_iff (P : GraphShiftedContactOperatorProblem V E)
    (f : GraphL2Product P.geometry) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) :
    (∀ v : GraphSobolevSpace P.geometry,
      P.operatorForm (graphSobolevSpaceOfEnergy P.geometry hu) v = P.operatorLoad f v) ↔
    (∀ (W : V → ℝ) (w : E → ℝ → ℝ), GraphEnergy P.geometry W w →
      graphShiftedContactForm P.geometry P.strength U W u w =
          ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, (f e) x * w e x) := by
  constructor
  · intro h W w hw
    have he := h (graphSobolevSpaceOfEnergy P.geometry hw)
    rwa [P.operatorForm_ofEnergy hu hw, P.operatorLoad_ofEnergy f hw] at he
  · intro h v
    have hv : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy v) = v :=
      graphSobolevSpaceOfEnergy_representative_eq P.geometry v
    rw [← hv]
    rw [P.operatorForm_ofEnergy hu (P.operatorRep_energy v),
      P.operatorLoad_ofEnergy f (P.operatorRep_energy v)]
    exact h (P.operatorNodes v) (P.operatorRep v) (P.operatorRep_energy v)

theorem GraphShiftedContactOperatorProblem.operatorSolution_physical (P : GraphShiftedContactOperatorProblem V E)
    (f : GraphL2Product P.geometry) :
    GraphShiftedContactL2WeakEquation P f (P.operatorNodes (P.operatorSolution f))
      (P.operatorRep (P.operatorSolution f)) := by
  refine ⟨P.operatorRep_energy (P.operatorSolution f), ?_⟩
  apply (P.operatorWeak_iff f (P.operatorRep_energy (P.operatorSolution f))).mp
  have hs : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy (P.operatorSolution f)) =
      P.operatorSolution f := graphSobolevSpaceOfEnergy_representative_eq P.geometry (P.operatorSolution f)
  rw [hs]
  intro v
  rw [P.operatorLoad_apply]
  exact P.operatorSolution_spec f v

theorem GraphShiftedContactL2WeakEquation.to_operatorSolution {P : GraphShiftedContactOperatorProblem V E}
    {f : GraphL2Product P.geometry} {U : V → ℝ} {u : E → ℝ → ℝ}
    (h : GraphShiftedContactL2WeakEquation P f U u) :
    graphSobolevSpaceOfEnergy P.geometry h.energy = P.operatorSolution f := by
  apply (P.operatorSolution_eq_iff f _).mpr
  have he := (P.operatorWeak_iff f h.energy).mpr h.weak_form
  simpa only [P.operatorLoad_apply] using he

theorem GraphShiftedContactL2WeakEquation.unique {P : GraphShiftedContactOperatorProblem V E}
    {f : GraphL2Product P.geometry} {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : GraphShiftedContactL2WeakEquation P f U u) (hw : GraphShiftedContactL2WeakEquation P f W w) :
    U = W ∧ ∀ e, EqOn (u e) (w e) (Icc 0 (P.geometry.length e)) := by
  constructor
  · rw [← P.operatorNodes_ofEnergy hu.energy, ← P.operatorNodes_ofEnergy hw.energy,
      hu.to_operatorSolution, hw.to_operatorSolution]
  · intro e
    have h₁ := P.operatorRep_ofEnergy hu.energy e
    have h₂ := P.operatorRep_ofEnergy hw.energy e
    rw [hu.to_operatorSolution] at h₁
    rw [hw.to_operatorSolution] at h₂
    exact h₁.symm.trans h₂

theorem GraphShiftedContactOperatorProblem.operator_physical_exists (P : GraphShiftedContactOperatorProblem V E)
    (f : GraphL2Product P.geometry) : ∃ U u, GraphShiftedContactL2WeakEquation P f U u :=
  ⟨P.operatorNodes (P.operatorSolution f), P.operatorRep (P.operatorSolution f),
    P.operatorSolution_physical f⟩

end TimeTraps.Analysis
