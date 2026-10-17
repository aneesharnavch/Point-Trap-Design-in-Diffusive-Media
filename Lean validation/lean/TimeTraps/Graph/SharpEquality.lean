module

public import TimeTraps.Graph.EqualityGeometry

@[expose] public section

/-!
Complete equality and constructive attainment for the constant-coefficient
graph bound. Balance and strength allocation are conditions on graph data;
the attaining profile is verified against the independent weak equation.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.boundHeight (G : MetricGraph V E) (κ : V → ℝ) : ℝ :=
  G.totalMass / (∑ v, κ v) + G.totalMass / (8 * ∑ e, 1 / G.adjustedResistance κ e)

def MetricGraph.HasBalancedMasses (G : MetricGraph V E) (κ : V → ℝ) : Prop :=
  ∀ e, G.adjustedResistance κ e * G.edgeMass e =
    G.totalMass / (∑ d, 1 / G.adjustedResistance κ d)

def MetricGraph.HasSharpStrengths (G : MetricGraph V E) (κ : V → ℝ) : Prop :=
  ∀ v, ¬G.IsPassiveTip κ v → κ v = (∑ w, κ w) / G.totalMass * G.coreLoad κ v

noncomputable def MetricGraph.sharpVertex (G : MetricGraph V E) (κ : V → ℝ) (v : V) : ℝ := by
  classical
  exact if G.IsPassiveTip κ v then G.boundHeight κ else G.totalMass / (∑ w, κ w)

omit [Nonempty E] in
theorem MetricGraph.no_two_passive_tips (G : MetricGraph V E) (κ : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) (e : E) :
    ¬(G.IsPassiveTip κ (G.tail e) ∧ G.IsPassiveTip κ (G.head e)) := by
  obtain ⟨U, u, j, hj⟩ := graph_state_exists G κ hκ hanchor
  exact hj.not_two_passive_tips e

omit [Fintype V] in
theorem GraphEquation.sharp_reactivity {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (M : ℝ)
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M)
    (heq : ∀ e, G.weakEdgeCost u M e = G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8)
    (v : V) (hv : ¬G.IsPassiveTip κ v) : 0 < κ v := by
  classical
  have hb := h.sharp_vertex_balance c M hM heq v
  rw [MetricGraph.sharpLoad, if_neg hv] at hb
  by_contra hn
  have hz : κ v = 0 := le_antisymm (le_of_not_gt hn) (hκ v)
  rw [hz, zero_mul] at hb
  have hp := G.coreLoad_pos κ v
  linarith

theorem WeakGraphEquation.equality_strengths {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (heq : G.essentialNorm u = G.boundHeight κ) :
    (∀ v, ¬G.IsPassiveTip κ v → 0 < κ v) ∧ G.HasSharpStrengths κ := by
  classical
  obtain ⟨hr, hp, _⟩ := (h.sharp_bound_eq_iff c hκ hanchor).mp heq
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  have hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ G.essentialNorm u := by
    intro e x hx
    rw [← h.maximum_eq_essentialNorm hκ hanchor]
    exact h.energy.le_maximum e hx
  have hreact := hj.sharp_reactivity c hκ (G.essentialNorm u) hM hp
  refine ⟨hreact, ?_⟩
  intro v hv
  have hb := hj.sharp_vertex_balance c (G.essentialNorm u) hM hp v
  rw [MetricGraph.sharpLoad, if_neg hv, hr v (hreact v hv)] at hb
  have hK : 0 < ∑ w, κ w := by
    obtain ⟨w, hw⟩ := hanchor
    exact Finset.sum_pos' (fun z _ => hκ z) ⟨w, Finset.mem_univ w, hw⟩
  field_simp [ne_of_gt hK, ne_of_gt G.totalMass_pos] at hb ⊢
  nlinarith

theorem WeakGraphEquation.equality_profiles {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (heq : G.essentialNorm u = G.boundHeight κ) :
    ∀ e, EqOn (u e) (c.sharpProfile κ (G.essentialNorm u) e) (Icc 0 (G.length e)) := by
  obtain ⟨_, hp, _⟩ := (h.sharp_bound_eq_iff c hκ hanchor).mp heq
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  intro e
  apply (hj.sharp_edge_profiles c (G.essentialNorm u) e ?_ (hp e)).1
  intro x hx
  rw [← h.maximum_eq_essentialNorm hκ hanchor]
  exact h.energy.le_maximum e hx

/-- Explicit parabolas and vertex values satisfy every edge equation, matching
condition and Kirchhoff law when the graph data have the stated allocations. -/
theorem MetricGraph.sharp_graph_equation (G : MetricGraph V E) (c : EdgeConstants G)
    (κ : V → ℝ) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (hbal : G.HasBalancedMasses κ) (hstrength : G.HasSharpStrengths κ) :
    GraphEquation G κ (G.sharpVertex κ) (c.sharpProfile κ (G.boundHeight κ)) (c.sharpFlux κ) := by
  classical
  have hno := G.no_two_passive_tips κ hκ hanchor
  have hK : 0 < ∑ w, κ w := by
    obtain ⟨w, hw⟩ := hanchor
    exact Finset.sum_pos' (fun z _ => hκ z) ⟨w, Finset.mem_univ w, hw⟩
  have hheight : G.boundHeight κ -
      (G.totalMass / (∑ d, 1 / G.adjustedResistance κ d)) / 8 = G.totalMass / (∑ w, κ w) := by
    unfold MetricGraph.boundHeight
    ring
  refine ⟨c.sharpProfile_equation κ (G.boundHeight κ), ?_, ?_, ?_⟩
  · intro e
    rw [(c.sharpProfile_endpoints κ (G.boundHeight κ) e (hno e)).1, hbal e]
    simp only [MetricGraph.sharpVertex, hheight]
  · intro e
    rw [(c.sharpProfile_endpoints κ (G.boundHeight κ) e (hno e)).2, hbal e]
    simp only [MetricGraph.sharpVertex, hheight]
  · intro v
    have hv : κ v * G.sharpVertex κ v = G.sharpLoad κ v := by
      unfold MetricGraph.sharpVertex MetricGraph.sharpLoad
      by_cases hp : G.IsPassiveTip κ v
      · simp [hp, hp.1]
      · rw [if_neg hp, if_neg hp, hstrength v hp]
        field_simp [ne_of_gt hK, ne_of_gt G.totalMass_pos]
    rw [hv, G.sharpLoad_eq_incidence κ v]
    unfold vertexFlux incidenceLoad
    apply Finset.sum_congr rfl
    intro e _
    dsimp only
    rw [(c.sharpFlux_endpoints κ e (hno e)).1, (c.sharpFlux_endpoints κ e (hno e)).2]

theorem MetricGraph.sharp_profile_attains (G : MetricGraph V E) (c : EdgeConstants G)
    (κ : V → ℝ) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (hbal : G.HasBalancedMasses κ) (hstrength : G.HasSharpStrengths κ) :
    WeakGraphEquation G κ (G.sharpVertex κ) (c.sharpProfile κ (G.boundHeight κ)) ∧
      G.essentialNorm (c.sharpProfile κ (G.boundHeight κ)) = G.boundHeight κ := by
  have hw := (G.sharp_graph_equation c κ hκ hanchor hbal hstrength).to_weak
  refine ⟨hw, le_antisymm ?_ ?_⟩
  · apply hw.energy.essentialNorm_le_iff.mpr
    intro e x hx
    rw [abs_of_pos ((hw.positive hκ hanchor).2 e x hx)]
    unfold EdgeConstants.sharpProfile
    exact sub_le_self _ (mul_nonneg (div_pos (c.source_pos e)
      (mul_pos (by positivity) (c.conductance_pos e))).le (sq_nonneg _))
  · let e : E := Classical.choice inferInstance
    have hM := hw.energy.essentialNorm_le_iff.mp
      (le_refl (G.essentialNorm (c.sharpProfile κ (G.boundHeight κ))))
    have hp := hM e (G.peakPosition κ e) (G.peakPosition_mem κ e)
    have he : c.sharpProfile κ (G.boundHeight κ) e (G.peakPosition κ e) = G.boundHeight κ := by
      simp [EdgeConstants.sharpProfile]
    rw [he] at hp
    exact (le_abs_self _).trans hp

omit [Fintype V] in
theorem GraphEnergy.essentialNorm_congr {G : MetricGraph V E} {U W : V → ℝ}
    {u w : E → ℝ → ℝ} (hu : GraphEnergy G U u) (hw : GraphEnergy G W w)
    (heq : ∀ e, EqOn (u e) (w e) (Icc 0 (G.length e))) : G.essentialNorm u = G.essentialNorm w := by
  apply le_antisymm
  · apply hu.essentialNorm_le_iff.mpr
    intro e x hx
    rw [heq e hx]
    exact hw.essentialNorm_le_iff.mp (le_refl _) e x hx
  · apply hw.essentialNorm_le_iff.mpr
    intro e x hx
    rw [← heq e hx]
    exact hu.essentialNorm_le_iff.mp (le_refl _) e x hx

/-- A characterization purely by physical graph data. The converse constructs
the state and uses weak uniqueness, rather than assuming sharp edge costs. -/
theorem WeakGraphEquation.sharp_eq_iff_balanced_strengths {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u = G.boundHeight κ ↔ G.HasBalancedMasses κ ∧ G.HasSharpStrengths κ := by
  constructor
  · intro heq
    exact ⟨((h.sharp_bound_eq_iff c hκ hanchor).mp heq).2.2,
      (h.equality_strengths c hκ hanchor heq).2⟩
  · rintro ⟨hbal, hstrength⟩
    obtain ⟨hw, hm⟩ := G.sharp_profile_attains c κ hκ hanchor hbal hstrength
    have he := weak_graph_state_unique h hw hκ hanchor
    exact (h.energy.essentialNorm_congr hw.energy he.2).trans hm

/-- The complete geometric equality classification, including every
non-passive vertex, both kinds of edge profile, and the strength formula. -/
theorem WeakGraphEquation.complete_graph_equality {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u = G.boundHeight κ ↔
      G.HasBalancedMasses κ ∧
      (∀ v, ¬G.IsPassiveTip κ v → 0 < κ v) ∧
      (∀ e, EqOn (u e) (c.sharpProfile κ (G.essentialNorm u) e) (Icc 0 (G.length e))) ∧
      G.HasSharpStrengths κ := by
  constructor
  · intro heq
    obtain ⟨hreact, hstrength⟩ := h.equality_strengths c hκ hanchor heq
    exact ⟨((h.sharp_bound_eq_iff c hκ hanchor).mp heq).2.2,
      hreact, h.equality_profiles c hκ hanchor heq, hstrength⟩
  · rintro ⟨hbal, _, _, hstrength⟩
    exact (h.sharp_eq_iff_balanced_strengths c hκ hanchor).mpr ⟨hbal, hstrength⟩

/-- Every attaining solution agrees with the explicit reconstruction, including
the vertex values at passive tips, throughout every physical closed edge. -/
theorem WeakGraphEquation.equality_reconstruction {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (heq : G.essentialNorm u = G.boundHeight κ) :
    U = G.sharpVertex κ ∧
      ∀ e, EqOn (u e) (c.sharpProfile κ (G.boundHeight κ) e) (Icc 0 (G.length e)) := by
  obtain ⟨hbal, hstrength⟩ := (h.sharp_eq_iff_balanced_strengths c hκ hanchor).mp heq
  exact weak_graph_state_unique h
    (G.sharp_graph_equation c κ hκ hanchor hbal hstrength).to_weak hκ hanchor

end TimeTraps.Graph
