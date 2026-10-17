module

public import TimeTraps.Graph.ProfilePhysical
public import TimeTraps.Graph.SharpDeficit

@[expose] public section

/-! The variable-profile bound for the independently defined physical weak
graph state, with exact deficit and complete local equality conditions.
No simultaneous attainability on an arbitrary graph is assumed. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis TimeTraps.Interval
open scoped BigOperators Classical

variable {V E : Type*}

noncomputable def MetricGraph.profileEdgeBarrier (G : MetricGraph V E) (κ : V → ℝ) (e : E) : ℝ :=
  if G.IsPassiveTip κ (G.head e) then profileCost (G.profileWeight e) (G.edgeMass e) 1
  else if G.IsPassiveTip κ (G.tail e) then profileCost (G.profileWeight e) (G.edgeMass e) 0
  else profileMinimum (G.profileWeight e) (G.edgeMass e)

def MetricGraph.profileEdgeEquality (G : MetricGraph V E) (κ U : V → ℝ)
    (u j : E → ℝ → ℝ) (M : ℝ) (e : E) : Prop :=
  if G.IsPassiveTip κ (G.head e) then M = U (G.head e)
  else if G.IsPassiveTip κ (G.tail e) then M = U (G.tail e)
  else (G.sourceInterval e).fluxLevel (j e) = profileMinimizer (G.profileWeight e) ∧
    M = (G.sourceInterval e).transformed (u e) (profileMinimizer (G.profileWeight e))

theorem MetricGraph.profileEdgeBarrier_pos (G : MetricGraph V E) (κ : V → ℝ) (e : E) :
    0 < G.profileEdgeBarrier κ e := by
  have hm := profile_moment_bounds (G.profileWeight e)
  unfold profileEdgeBarrier
  split_ifs
  · rw [profileCost_one]
    exact mul_pos (G.edgeMass_pos e) (sub_pos.mpr hm.2)
  · rw [profileCost_zero]
    exact mul_pos (G.edgeMass_pos e) hm.1
  · exact profileMinimum_pos (G.profileWeight e) (G.edgeMass_pos e)

variable [Fintype E]

theorem GraphEquation.profile_edge_bound {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) :
    G.profileEdgeBarrier κ e ≤ G.weakEdgeCost u M e := by
  unfold MetricGraph.profileEdgeBarrier
  split_ifs with hh ht
  · exact h.profile_head_bound M e hh hM
  · exact h.profile_tail_bound M e ht hM
  · exact h.profile_ordinary_bound M e hM

theorem GraphEquation.profile_edge_eq_iff {G : MetricGraph V E} {κ U : V → ℝ}
    {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (M : ℝ) (e : E)
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M) :
    G.weakEdgeCost u M e = G.profileEdgeBarrier κ e ↔
      G.profileEdgeEquality κ U u j M e := by
  unfold MetricGraph.profileEdgeBarrier MetricGraph.profileEdgeEquality
  split_ifs with hh ht
  · exact h.profile_head_eq_iff M e hh
  · exact h.profile_tail_eq_iff M e ht
  · exact h.profile_ordinary_eq_iff M e hM

variable [Fintype V] [Nonempty E]

noncomputable def MetricGraph.profileEdgeDeficit (G : MetricGraph V E) (κ : V → ℝ)
    (u : E → ℝ → ℝ) : ℝ :=
  (∑ e, (G.weakEdgeCost u (G.essentialNorm u) e - G.profileEdgeBarrier κ e)) / G.totalMass

theorem WeakGraphEquation.profile_deficit_identity {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u - G.totalMass / (∑ v, κ v) -
      (∑ e, G.profileEdgeBarrier κ e) / G.totalMass =
        G.reactionDeficit κ U + G.profileEdgeDeficit κ u := by
  have hK : 0 < ∑ v, κ v := by
    obtain ⟨v, hv⟩ := hanchor
    exact Finset.sum_pos' (fun w _ => hκ w) ⟨v, Finset.mem_univ v, hv⟩
  have hv := weighted_variance_identity Finset.univ κ U (ne_of_gt hK) rfl h.conservation
  have he := h.cost_energy_identity hκ hanchor (G.essentialNorm u)
  unfold MetricGraph.reactionDeficit MetricGraph.profileEdgeDeficit
  rw [hv, Finset.sum_sub_distrib]
  field_simp [ne_of_gt hK, ne_of_gt G.totalMass_pos]
  linear_combination (∑ v, κ v) * he

theorem WeakGraphEquation.profile_deficits_nonneg {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    0 ≤ G.reactionDeficit κ U ∧ 0 ≤ G.profileEdgeDeficit κ u := by
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  have hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ G.essentialNorm u := by
    intro e x hx
    exact (le_abs_self _).trans ((h.energy.essentialNorm_le_iff.mp le_rfl) e x hx)
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun v _ => mul_nonneg (hκ v) (sq_nonneg _)))
      G.totalMass_pos.le
  · exact div_nonneg (Finset.sum_nonneg
      (fun e _ => sub_nonneg.mpr (hj.profile_edge_bound (G.essentialNorm u) e hM)))
      G.totalMass_pos.le

theorem WeakGraphEquation.profile_bound {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.totalMass / (∑ v, κ v) + (∑ e, G.profileEdgeBarrier κ e) / G.totalMass ≤
      G.essentialNorm u := by
  have he := h.profile_deficit_identity hκ hanchor
  have hn := h.profile_deficits_nonneg hκ hanchor
  linarith

theorem WeakGraphEquation.profileEdgeDeficit_zero_iff {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.profileEdgeDeficit κ u = 0 ↔
      ∀ e, G.weakEdgeCost u (G.essentialNorm u) e = G.profileEdgeBarrier κ e := by
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  have hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ G.essentialNorm u := by
    intro e x hx
    exact (le_abs_self _).trans ((h.energy.essentialNorm_le_iff.mp le_rfl) e x hx)
  unfold MetricGraph.profileEdgeDeficit
  simp only [div_eq_zero_iff, ne_of_gt G.totalMass_pos, or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => sub_nonneg.mpr (hj.profile_edge_bound (G.essentialNorm u) e hM))]
  simp only [Finset.mem_univ, forall_true_left, sub_eq_zero]

theorem WeakGraphEquation.profile_bound_eq_iff_costs {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u = G.totalMass / (∑ v, κ v) +
        (∑ e, G.profileEdgeBarrier κ e) / G.totalMass ↔
      (∀ v, 0 < κ v → U v = G.totalMass / (∑ w, κ w)) ∧
      ∀ e, G.weakEdgeCost u (G.essentialNorm u) e = G.profileEdgeBarrier κ e := by
  rw [← h.reactionDeficit_zero_iff hκ hanchor, ← h.profileEdgeDeficit_zero_iff hκ hanchor]
  have he := h.profile_deficit_identity hκ hanchor
  have hn := h.profile_deficits_nonneg hκ hanchor
  constructor
  · intro hz
    constructor <;> linarith
  · rintro ⟨hr, hp⟩
    linarith

theorem GraphEquation.profile_bound_eq_iff {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u = G.totalMass / (∑ v, κ v) +
        (∑ e, G.profileEdgeBarrier κ e) / G.totalMass ↔
      (∀ v, 0 < κ v → U v = G.totalMass / (∑ w, κ w)) ∧
      ∀ e, G.profileEdgeEquality κ U u j (G.essentialNorm u) e := by
  have hw := h.to_weak
  have hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ G.essentialNorm u := by
    intro e x hx
    exact (le_abs_self _).trans ((hw.energy.essentialNorm_le_iff.mp le_rfl) e x hx)
  rw [hw.profile_bound_eq_iff_costs hκ hanchor]
  apply and_congr_right
  intro _
  exact forall_congr' (fun e => h.profile_edge_eq_iff (G.essentialNorm u) e hM)

theorem WeakGraphEquation.profile_bound_eq_iff {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u = G.totalMass / (∑ v, κ v) +
        (∑ e, G.profileEdgeBarrier κ e) / G.totalMass ↔
      ∃ j, GraphEquation G κ U u j ∧
        (∀ v, 0 < κ v → U v = G.totalMass / (∑ w, κ w)) ∧
        ∀ e, G.profileEdgeEquality κ U u j (G.essentialNorm u) e := by
  constructor
  · intro he
    obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
    exact ⟨j, hj, (hj.profile_bound_eq_iff hκ hanchor).mp he⟩
  · rintro ⟨j, hj, he⟩
    exact (hj.profile_bound_eq_iff hκ hanchor).mpr he

end TimeTraps.Graph
