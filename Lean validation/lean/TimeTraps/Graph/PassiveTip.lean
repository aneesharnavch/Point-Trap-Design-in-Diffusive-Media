module

public import TimeTraps.Graph.MetricState

@[expose] public section

/-!
Degree-one endpoints and passive reflection are defined by incidence, before
any solution is given. A loop has two distinct edge ends and cannot supply a
degree-one tip. The Neumann condition is derived from the vertex equation.
-/

namespace TimeTraps.Graph

open scoped BigOperators

variable {V E : Type*}

def MetricGraph.endVertex (G : MetricGraph V E) (s : E × Bool) : V :=
  if s.2 then G.head s.1 else G.tail s.1

def MetricGraph.IsTip (G : MetricGraph V E) (v : V) : Prop :=
  ∃! s : E × Bool, G.endVertex s = v

noncomputable def MetricGraph.degree [Fintype E] (G : MetricGraph V E) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : E × Bool => G.endVertex s = v).card

def MetricGraph.IsPassiveTip (G : MetricGraph V E) (κ : V → ℝ) (v : V) : Prop :=
  κ v = 0 ∧ G.IsTip v

noncomputable def MetricGraph.reflectionFactor (G : MetricGraph V E) (κ : V → ℝ) (e : E) : ℝ := by
  classical
  exact if G.IsPassiveTip κ (G.tail e) ∨ G.IsPassiveTip κ (G.head e) then 4 else 1

noncomputable def MetricGraph.adjustedResistance (G : MetricGraph V E) (κ : V → ℝ) (e : E) : ℝ :=
  G.reflectionFactor κ e * G.resistance e

theorem MetricGraph.degree_one_iff [Fintype E] (G : MetricGraph V E) (v : V) :
    G.degree v = 1 ↔ G.IsTip v := by
  classical
  simp only [MetricGraph.degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp [MetricGraph.IsTip]

theorem MetricGraph.tip_tail_incidence (G : MetricGraph V E) (e : E) (htip : G.IsTip (G.tail e)) :
    (∀ d, G.tail d = G.tail e ↔ d = e) ∧ (∀ d, G.head d ≠ G.tail e) := by
  have huniq : ∀ s, G.endVertex s = G.tail e → s = (e, false) := by
    intro s hs
    exact htip.unique hs (by simp [MetricGraph.endVertex])
  constructor
  · intro d
    constructor
    · intro hd
      exact congrArg Prod.fst (huniq (d, false) (by simpa [MetricGraph.endVertex] using hd))
    · rintro rfl
      rfl
  · intro d hd
    have heq := congrArg Prod.snd (huniq (d, true) (by simpa [MetricGraph.endVertex] using hd))
    simp at heq

theorem MetricGraph.tip_head_incidence (G : MetricGraph V E) (e : E) (htip : G.IsTip (G.head e)) :
    (∀ d, G.tail d ≠ G.head e) ∧ (∀ d, G.head d = G.head e ↔ d = e) := by
  have huniq : ∀ s, G.endVertex s = G.head e → s = (e, true) := by
    intro s hs
    exact htip.unique hs (by simp [MetricGraph.endVertex])
  constructor
  · intro d hd
    have heq := congrArg Prod.snd (huniq (d, false) (by simpa [MetricGraph.endVertex] using hd))
    simp at heq
  · intro d
    constructor
    · intro hd
      exact congrArg Prod.fst (huniq (d, true) (by simpa [MetricGraph.endVertex] using hd))
    · rintro rfl
      rfl

theorem MetricGraph.loop_not_tip (G : MetricGraph V E) (e : E) (he : G.tail e = G.head e) :
    ¬G.IsTip (G.tail e) := by
  intro htip
  exact (G.tip_tail_incidence e htip).2 e he.symm

theorem MetricGraph.tip_tail_flux [Fintype E] (G : MetricGraph V E) (e : E)
    (htip : G.IsTip (G.tail e)) (j₀ j₁ : E → ℝ) :
    vertexFlux G.tail G.head j₀ j₁ (G.tail e) = j₀ e := by
  classical
  obtain ⟨ht, hh⟩ := G.tip_tail_incidence e htip
  simp [vertexFlux, incidenceLoad, ht, hh]

theorem MetricGraph.tip_head_flux [Fintype E] (G : MetricGraph V E) (e : E)
    (htip : G.IsTip (G.head e)) (j₀ j₁ : E → ℝ) :
    vertexFlux G.tail G.head j₀ j₁ (G.head e) = -j₁ e := by
  classical
  obtain ⟨ht, hh⟩ := G.tip_head_incidence e htip
  simp [vertexFlux, incidenceLoad, ht, hh]

theorem GraphEquation.passive_tail_neumann [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) {e : E}
    (htip : G.IsPassiveTip κ (G.tail e)) : j e 0 = 0 := by
  have hb := h.vertex_balance (G.tail e)
  rw [htip.1, zero_mul, G.tip_tail_flux e htip.2] at hb
  exact hb.symm

theorem GraphEquation.passive_head_neumann [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) {e : E}
    (htip : G.IsPassiveTip κ (G.head e)) : j e (G.length e) = 0 := by
  have hb := h.vertex_balance (G.head e)
  rw [htip.1, zero_mul, G.tip_head_flux e htip.2] at hb
  linarith

theorem MetricGraph.reflectionFactor_pos (G : MetricGraph V E) (κ : V → ℝ) (e : E) :
    0 < G.reflectionFactor κ e := by
  unfold MetricGraph.reflectionFactor
  split_ifs <;> positivity

theorem MetricGraph.adjustedResistance_pos (G : MetricGraph V E) (κ : V → ℝ) (e : E) :
    0 < G.adjustedResistance κ e :=
  mul_pos (G.reflectionFactor_pos κ e) (G.resistance_pos e)

end TimeTraps.Graph
