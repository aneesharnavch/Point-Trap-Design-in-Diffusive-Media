module

public import TimeTraps.Graph.ProfileConsistency
public import TimeTraps.Graph.ProfileBarrier
public import TimeTraps.Graph.SourceCoordinates

@[expose] public section

/-!
Sharp profile costs for the actual graph state and its physical edge cost.
Only positive continuous source and conductance are used. The deficit
profile and its derivative are derived from the graph equation, including
the incidence-derived passive endpoint conditions.
-/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis TimeTraps.Interval

variable {V E : Type*} [Fintype E] {G : MetricGraph V E} {κ U : V → ℝ}
  {u j : E → ℝ → ℝ}

theorem GraphEquation.profile_equation (h : GraphEquation G κ U u j) (M : ℝ) (e : E) :
    ProfileEquation (G.profileWeight e) ((G.sourceInterval e).fluxLevel (j e))
      (fun z => M - (G.sourceInterval e).transformed (u e) z) := by
  constructor
  · exact (continuous_const.sub ((G.sourceInterval e).transformed_continuous
      (h.edge_equation e).state_continuous)).continuousOn
  · intro z hz
    exact h.source_deficit_derivative M e hz

theorem GraphEquation.profile_edge_cost (h : GraphEquation G κ U u j) (M : ℝ) (e : E) :
    G.weakEdgeCost u M e = profileIntegralCost (G.profileWeight e) (G.edgeMass e)
      ((G.sourceInterval e).fluxLevel (j e))
      (fun z => M - (G.sourceInterval e).transformed (u e) z) := by
  rw [h.weakEdgeCost_eq M e]
  exact h.source_edge_cost M e

theorem GraphEquation.profile_ordinary_bound (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) :
    profileMinimum (G.profileWeight e) (G.edgeMass e) ≤ G.weakEdgeCost u M e := by
  rw [h.profile_edge_cost M e]
  apply (h.profile_equation M e).minimum_le_cost (G.edgeMass_pos e)
  intro z _
  exact sub_nonneg.mpr (hM e _ ((G.sourceInterval e).inverse_mem z))

theorem GraphEquation.profile_ordinary_eq_iff (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) :
    G.weakEdgeCost u M e = profileMinimum (G.profileWeight e) (G.edgeMass e) ↔
      (G.sourceInterval e).fluxLevel (j e) = profileMinimizer (G.profileWeight e) ∧
      M = (G.sourceInterval e).transformed (u e) (profileMinimizer (G.profileWeight e)) := by
  rw [h.profile_edge_cost M e,
    (h.profile_equation M e).cost_eq_minimum_iff (G.edgeMass_pos e)
      (fun z _ => sub_nonneg.mpr (hM e _ ((G.sourceInterval e).inverse_mem z)))]
  constructor
  · rintro ⟨ha, hy⟩
    rw [ha] at hy
    exact ⟨ha, sub_eq_zero.mp hy⟩
  · rintro ⟨ha, hy⟩
    refine ⟨ha, ?_⟩
    rw [ha]
    exact sub_eq_zero.mpr hy

theorem GraphEquation.profile_head_bound (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (htip : G.IsPassiveTip κ (G.head e))
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) :
    profileCost (G.profileWeight e) (G.edgeMass e) 1 ≤ G.weakEdgeCost u M e := by
  have he := h.profile_equation M e
  have ha := h.passive_head_source_level htip
  rw [ha] at he
  rw [h.profile_edge_cost M e, ha, profileCost_one]
  apply he.passive_head_bound (G.edgeMass_pos e)
  simp only [SourceInterval.transformed, Function.comp_apply, SourceInterval.inverse_one]
  exact sub_nonneg.mpr (hM e _ ⟨(G.length_pos e).le, le_rfl⟩)

theorem GraphEquation.profile_head_eq_iff (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (htip : G.IsPassiveTip κ (G.head e)) :
    G.weakEdgeCost u M e = profileCost (G.profileWeight e) (G.edgeMass e) 1 ↔
      M = U (G.head e) := by
  have he := h.profile_equation M e
  have ha := h.passive_head_source_level htip
  rw [ha] at he
  rw [h.profile_edge_cost M e, ha, profileCost_one,
    he.passive_head_eq_iff (G.edgeMass_pos e)]
  simp only [SourceInterval.transformed, Function.comp_apply, SourceInterval.inverse_one]
  change M - u e (G.length e) = 0 ↔ M = U (G.head e)
  rw [h.head_value e, sub_eq_zero]

theorem GraphEquation.profile_tail_bound (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (htip : G.IsPassiveTip κ (G.tail e))
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) :
    profileCost (G.profileWeight e) (G.edgeMass e) 0 ≤ G.weakEdgeCost u M e := by
  have he := h.profile_equation M e
  have ha := h.passive_tail_source_level htip
  rw [ha] at he
  rw [h.profile_edge_cost M e, ha, profileCost_zero]
  apply he.passive_tail_bound (G.edgeMass_pos e)
  simp only [SourceInterval.transformed, Function.comp_apply, SourceInterval.inverse_zero]
  exact sub_nonneg.mpr (hM e _ ⟨le_rfl, (G.length_pos e).le⟩)

theorem GraphEquation.profile_tail_eq_iff (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (htip : G.IsPassiveTip κ (G.tail e)) :
    G.weakEdgeCost u M e = profileCost (G.profileWeight e) (G.edgeMass e) 0 ↔
      M = U (G.tail e) := by
  have he := h.profile_equation M e
  have ha := h.passive_tail_source_level htip
  rw [ha] at he
  rw [h.profile_edge_cost M e, ha, profileCost_zero,
    he.passive_tail_eq_iff (G.edgeMass_pos e)]
  simp only [SourceInterval.transformed, Function.comp_apply, SourceInterval.inverse_zero]
  change M - u e 0 = 0 ↔ M = U (G.tail e)
  rw [h.tail_value e, sub_eq_zero]

end TimeTraps.Graph
