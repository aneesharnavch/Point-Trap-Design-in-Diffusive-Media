module

public import TimeTraps.Analysis.GraphSobolevProductCompact
public import TimeTraps.Analysis.IntervalSobolevSpaceEvaluation

@[expose] public section

/-! Vertex-continuous graph H1 is a closed subspace of the actual edge
Hilbert product. The two ends of a loop remain distinct endpoints; any
endpoint pair attached to the same vertex has equal traces. No separate
nodal coordinates, incidence coverage, or nonempty-edge premise is used. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*}

def graphEndpointVertex (G : MetricGraph V E) : E ⊕ E → V := Sum.elim G.tail G.head

noncomputable def graphEndpointTraceL (G : MetricGraph V E) :
    E ⊕ E → (GraphSobolevProduct G →L[ℝ] ℝ)
  | .inl e => (evalL (G.length_pos e) 0 ⟨le_rfl, (G.length_pos e).le⟩).comp
      (graphSobolevComponentL G e)
  | .inr e => (evalL (G.length_pos e) (G.length e) ⟨(G.length_pos e).le, le_rfl⟩).comp
      (graphSobolevComponentL G e)

theorem graphEndpointTraceL_tail (G : MetricGraph V E) (u : GraphSobolevProduct G) (e : E) :
    graphEndpointTraceL G (.inl e) u = (u e).representative (G.length_pos e) 0 := rfl

theorem graphEndpointTraceL_head (G : MetricGraph V E) (u : GraphSobolevProduct G) (e : E) :
    graphEndpointTraceL G (.inr e) u = (u e).representative (G.length_pos e) (G.length e) := rfl

noncomputable def graphSobolevSubspace (G : MetricGraph V E) :
    Submodule ℝ (GraphSobolevProduct G) :=
  ⨅ a : E ⊕ E, ⨅ b : E ⊕ E, ⨅ _ : graphEndpointVertex G a = graphEndpointVertex G b,
    (graphEndpointTraceL G a - graphEndpointTraceL G b).ker

theorem graphSobolevSubspace_mem_iff (G : MetricGraph V E) (u : GraphSobolevProduct G) :
    u ∈ graphSobolevSubspace G ↔ ∀ a b,
      graphEndpointVertex G a = graphEndpointVertex G b →
        graphEndpointTraceL G a u = graphEndpointTraceL G b u := by
  simp only [graphSobolevSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, sub_apply, sub_eq_zero]

theorem graphSobolevSubspace_isClosed (G : MetricGraph V E) :
    IsClosed (graphSobolevSubspace G : Set (GraphSobolevProduct G)) := by
  unfold graphSobolevSubspace
  simp only [Submodule.coe_iInf]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    (graphEndpointTraceL G a - graphEndpointTraceL G b).isClosed_ker

abbrev GraphSobolevSpace (G : MetricGraph V E) := ↥(graphSobolevSubspace G)

instance graphSobolevSpace_complete (G : MetricGraph V E) :
    CompleteSpace (GraphSobolevSpace G) := (graphSobolevSubspace_isClosed G).completeSpace_coe

noncomputable def graphSobolevSpaceStateL (G : MetricGraph V E) :
    GraphSobolevSpace G →L[ℝ] GraphL2Product G :=
  (graphSobolevStateL G).comp (graphSobolevSubspace G).subtypeL

theorem graphSobolevSpaceStateL_apply (G : MetricGraph V E)
    (u : GraphSobolevSpace G) (e : E) : (graphSobolevSpaceStateL G u) e = (u.val e).state := rfl

theorem graphSobolevSpaceStateL_injective (G : MetricGraph V E) :
    Function.Injective (graphSobolevSpaceStateL G) := by
  intro u v h
  apply Subtype.ext
  exact graphSobolevStateL_injective G h

theorem graphSobolevSpaceStateL_compact [Fintype E] (G : MetricGraph V E) :
    IsCompactOperator (graphSobolevSpaceStateL G) :=
  (graphSobolevStateL_compact G).comp_clm (graphSobolevSubspace G).subtypeL

end TimeTraps.Analysis
