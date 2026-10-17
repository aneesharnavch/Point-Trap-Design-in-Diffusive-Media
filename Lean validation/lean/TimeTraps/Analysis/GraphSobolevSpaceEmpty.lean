module

public import TimeTraps.Analysis.GraphSobolevSpace
public import TimeTraps.Graph.WeakState

@[expose] public section

/-! With no edges the edge Sobolev space is trivial, while arbitrary
vertex values satisfy the original edge-energy matching conditions.
Thus edge L2 data alone do not determine the isolated vertex value. -/

namespace TimeTraps.Analysis

open TimeTraps.Graph

variable {V E : Type*} [IsEmpty E]

theorem graphEmpty_vertices_subsingleton (G : MetricGraph V E) : Subsingleton V := by
  constructor
  intro v w
  induction G.connected v w with
  | rel v w h =>
      obtain ⟨e, _⟩ := h
      exact isEmptyElim e
  | refl v => rfl
  | symm v w _ ih => exact ih.symm
  | trans v w z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem graphEnergy_empty (G : MetricGraph V E) (U : V → ℝ) (u : E → ℝ → ℝ) :
    GraphEnergy G U u :=
  ⟨fun e => isEmptyElim e, fun e => isEmptyElim e, fun e => isEmptyElim e⟩

theorem graphSobolevSpace_empty_subsingleton (G : MetricGraph V E)
    (u v : GraphSobolevSpace G) : u = v := by
  apply Subtype.ext
  apply PiLp.ext
  intro e
  exact isEmptyElim e

theorem graphSobolevSpace_empty_nodal_ambiguity [Nonempty V] (G : MetricGraph V E)
    (u : E → ℝ → ℝ) :
    ∃ U W : V → ℝ, U ≠ W ∧ GraphEnergy G U u ∧ GraphEnergy G W u := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, graphEnergy_empty G _ u, graphEnergy_empty G _ u⟩
  intro h
  have he := congrFun h (Classical.choice inferInstance)
  exact zero_ne_one he

end TimeTraps.Analysis
