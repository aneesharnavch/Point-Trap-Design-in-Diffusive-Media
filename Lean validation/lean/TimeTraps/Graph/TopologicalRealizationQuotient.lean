module

public import TimeTraps.Graph.TopologicalRealization
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

/-! The realized finite graph has exactly the quotient topology of its
closed physical edges. Thus continuous functions are characterized by
their continuous edge pullbacks, with no chosen inverse topology. -/

namespace TimeTraps.Graph

open Set Topology

variable {V E : Type*}

noncomputable def MetricGraph.realizationMap (G : MetricGraph V E)
    (p : GraphClosedEdgePoint G) : GraphRealization G := G.edgePoint p.1 p.2

theorem MetricGraph.realizationMap_continuous (G : MetricGraph V E) :
    Continuous G.realizationMap := continuous_sigma G.edgePoint_continuous

theorem MetricGraph.realizationMap_surjective (G : MetricGraph V E) :
    Function.Surjective G.realizationMap := by
  intro p
  obtain ⟨e, x, hx⟩ := G.edgePoint_surjective p
  exact ⟨⟨e, x⟩, hx⟩

variable [Fintype E]

theorem MetricGraph.realizationMap_quotient (G : MetricGraph V E) :
    IsQuotientMap G.realizationMap :=
  IsQuotientMap.of_surjective_continuous G.realizationMap_surjective G.realizationMap_continuous

theorem MetricGraph.realization_continuous_iff (G : MetricGraph V E)
    {Y : Type*} [TopologicalSpace Y] (f : GraphRealization G → Y) :
    Continuous f ↔ ∀ e, Continuous (fun x => f (G.edgePoint e x)) := by
  rw [G.realizationMap_quotient.continuous_iff, continuous_sigma_iff]
  rfl

end TimeTraps.Graph
