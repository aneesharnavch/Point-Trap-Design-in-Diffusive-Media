module

public import TimeTraps.Graph.TopologicalRealizationVertices
public import TimeTraps.Graph.TopologicalRealizationQuotient

@[expose] public section

/-! Exact descent of vertex-compatible edge functions to the realized
graph. The values agree for every representation of a vertex; continuity
is derived from the proved compact quotient map. -/

namespace TimeTraps.Graph

open Set

variable {V E Y : Type*}

noncomputable def MetricGraph.realizationDescend (G : MetricGraph V E)
    (f : GraphClosedEdgePoint G → Y) (p : GraphRealization G) : Y :=
  f (Function.surjInv G.realizationMap_surjective p)

theorem MetricGraph.realizationDescend_apply (G : MetricGraph V E)
    (f : GraphClosedEdgePoint G → Y)
    (hf : ∀ p q, G.realizationMap p = G.realizationMap q → f p = f q)
    (p : GraphClosedEdgePoint G) : G.realizationDescend f (G.realizationMap p) = f p :=
  hf _ p (Function.surjInv_eq G.realizationMap_surjective (G.realizationMap p))

theorem MetricGraph.realizationDescend_continuous [Fintype E] [TopologicalSpace Y]
    (G : MetricGraph V E) (f : GraphClosedEdgePoint G → Y) (hc : Continuous f)
    (hf : ∀ p q, G.realizationMap p = G.realizationMap q → f p = f q) :
    Continuous (G.realizationDescend f) := by
  apply G.realizationMap_quotient.continuous_iff.mpr
  simpa only [Function.comp_def, G.realizationDescend_apply f hf] using hc

theorem graphTrace_endpoint (G : MetricGraph V E) (U : V → Y)
    (u : ∀ e, Icc (0 : ℝ) (G.length e) → Y)
    (htail : ∀ e, u e ⟨0, le_rfl, (G.length_pos e).le⟩ = U (G.tail e))
    (hhead : ∀ e, u e ⟨G.length e, (G.length_pos e).le, le_rfl⟩ = U (G.head e))
    (e : E) (x : Icc (0 : ℝ) (G.length e)) (v : V) (hx : GraphEndpointAt G e x.val v) :
    u e x = U v := by
  rcases hx with ⟨hx, hv⟩ | ⟨hx, hv⟩
  · exact (congrArg (u e) (Subtype.ext hx)).trans ((htail e).trans (congrArg U hv))
  · exact (congrArg (u e) (Subtype.ext hx)).trans ((hhead e).trans (congrArg U hv))

theorem graphTrace_fiber (G : MetricGraph V E) (U : V → Y)
    (u : ∀ e, Icc (0 : ℝ) (G.length e) → Y)
    (htail : ∀ e, u e ⟨0, le_rfl, (G.length_pos e).le⟩ = U (G.tail e))
    (hhead : ∀ e, u e ⟨G.length e, (G.length_pos e).le, le_rfl⟩ = U (G.head e))
    (p q : GraphClosedEdgePoint G) (hpq : G.realizationMap p = G.realizationMap q) :
    u p.1 p.2 = u q.1 q.2 := by
  obtain h | ⟨v, hp, hq⟩ := (G.edgePoint_fiber_iff p.1 q.1 p.2 q.2).mp hpq
  · exact congrArg (fun z : GraphClosedEdgePoint G => u z.1 z.2) h
  · exact (graphTrace_endpoint G U u htail hhead p.1 p.2 v hp).trans
      (graphTrace_endpoint G U u htail hhead q.1 q.2 v hq).symm

noncomputable def MetricGraph.realizationTrace (G : MetricGraph V E)
    (u : ∀ e, Icc (0 : ℝ) (G.length e) → Y) : GraphRealization G → Y :=
  G.realizationDescend (fun p => u p.1 p.2)

theorem MetricGraph.realizationTrace_apply (G : MetricGraph V E) (U : V → Y)
    (u : ∀ e, Icc (0 : ℝ) (G.length e) → Y)
    (htail : ∀ e, u e ⟨0, le_rfl, (G.length_pos e).le⟩ = U (G.tail e))
    (hhead : ∀ e, u e ⟨G.length e, (G.length_pos e).le, le_rfl⟩ = U (G.head e))
    (e : E) (x : Icc (0 : ℝ) (G.length e)) : G.realizationTrace u (G.edgePoint e x) = u e x :=
  G.realizationDescend_apply _ (graphTrace_fiber G U u htail hhead) ⟨e, x⟩

theorem MetricGraph.realizationTrace_continuous [Fintype E] [TopologicalSpace Y]
    (G : MetricGraph V E) (U : V → Y) (u : ∀ e, Icc (0 : ℝ) (G.length e) → Y)
    (hc : ∀ e, Continuous (u e))
    (htail : ∀ e, u e ⟨0, le_rfl, (G.length_pos e).le⟩ = U (G.tail e))
    (hhead : ∀ e, u e ⟨G.length e, (G.length_pos e).le, le_rfl⟩ = U (G.head e)) :
    Continuous (G.realizationTrace u) :=
  G.realizationDescend_continuous _ (continuous_sigma hc) (graphTrace_fiber G U u htail hhead)

end TimeTraps.Graph
