module

public import TimeTraps.Graph.StateMaximum

@[expose] public section

/-!
The exact graph deficit with the actual essential norm and incidence-defined
reflection factors. All three terms are nonnegative, and their simultaneous
zero conditions characterize equality in the final numerical bound.
The geometric reconstruction and vertex strength formula remain separate.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.reactionDeficit (G : MetricGraph V E) (κ U : V → ℝ) : ℝ :=
  (∑ v, κ v * (U v - G.totalMass / (∑ w, κ w)) ^ 2) / G.totalMass

noncomputable def MetricGraph.profileDeficit (G : MetricGraph V E) (κ : V → ℝ) (u : E → ℝ → ℝ) : ℝ :=
  (∑ e, (G.weakEdgeCost u (G.essentialNorm u) e -
    G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8)) / G.totalMass

noncomputable def MetricGraph.resistanceDeficit (G : MetricGraph V E) (κ : V → ℝ) : ℝ :=
  (∑ e, (G.adjustedResistance κ e * G.edgeMass e -
    G.totalMass / (∑ d, 1 / G.adjustedResistance κ d)) ^ 2 / G.adjustedResistance κ e) /
      (8 * G.totalMass)

theorem WeakGraphEquation.sharp_deficit_identity {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u - G.totalMass / (∑ v, κ v) -
      G.totalMass / (8 * ∑ e, 1 / G.adjustedResistance κ e) =
        G.reactionDeficit κ U + G.profileDeficit κ u + G.resistanceDeficit κ := by
  have hK : 0 < ∑ v, κ v := by
    obtain ⟨v, hv⟩ := hanchor
    exact Finset.sum_pos' (fun w _ => hκ w) ⟨v, Finset.mem_univ v, hv⟩
  have hC : 0 < ∑ e, 1 / G.adjustedResistance κ e :=
    Finset.sum_pos (fun e _ => one_div_pos.mpr (G.adjustedResistance_pos κ e)) Finset.univ_nonempty
  exact finite_graph_deficit κ U (G.adjustedResistance κ) G.edgeMass
    (G.weakEdgeCost u (G.essentialNorm u)) (ne_of_gt G.totalMass_pos)
    (ne_of_gt hK) (ne_of_gt hC) (G.adjustedResistance_pos κ) rfl h.conservation rfl rfl
    (h.cost_energy_identity hκ hanchor (G.essentialNorm u))

theorem WeakGraphEquation.sharp_deficit_nonneg {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    0 ≤ G.reactionDeficit κ U ∧ 0 ≤ G.profileDeficit κ u ∧ 0 ≤ G.resistanceDeficit κ := by
  have hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ G.essentialNorm u := by
    intro e x hx
    rw [← h.maximum_eq_essentialNorm hκ hanchor]
    exact h.energy.le_maximum e hx
  refine ⟨?_, ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg (fun v _ => mul_nonneg (hκ v) (sq_nonneg _)))
      G.totalMass_pos.le
  · exact div_nonneg (Finset.sum_nonneg (fun e _ => h.edge_excess_nonneg c hκ hanchor hM e))
      G.totalMass_pos.le
  · exact div_nonneg (Finset.sum_nonneg fun e _ =>
      div_nonneg (sq_nonneg _) (G.adjustedResistance_pos κ e).le)
      (mul_nonneg (by positivity) G.totalMass_pos.le)

/-- The reaction term is exactly the absorption-share pair term in the paper;
half the ordered double sum counts each unordered pair once. -/
theorem WeakGraphEquation.reactionDeficit_pairwise {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.reactionDeficit κ U = G.totalMass / (∑ v, κ v) * ((1 / 2 : ℝ) * ∑ v, ∑ w,
      (κ v * U v / G.totalMass) * (κ w * U w / G.totalMass) *
        (U v - U w) ^ 2 / (U v * U w)) := by
  have hK : 0 < ∑ v, κ v := by
    obtain ⟨v, hv⟩ := hanchor
    exact Finset.sum_pos' (fun w _ => hκ w) ⟨v, Finset.mem_univ v, hv⟩
  exact reaction_deficit_pairwise κ U (ne_of_gt G.totalMass_pos) (ne_of_gt hK)
    (fun v => ne_of_gt ((h.positive hκ hanchor).1 v)) rfl h.conservation

omit [Fintype V] in
/-- The resistance term is C/(8V) times the normalized weighted variance. -/
theorem MetricGraph.resistanceDeficit_normalized (G : MetricGraph V E) (κ : V → ℝ) :
    G.resistanceDeficit κ = (∑ e, 1 / G.adjustedResistance κ e) / (8 * G.totalMass) *
      (∑ e, 1 / (G.adjustedResistance κ e * ∑ d, 1 / G.adjustedResistance κ d) *
        (G.adjustedResistance κ e * G.edgeMass e -
          G.totalMass / (∑ d, 1 / G.adjustedResistance κ d)) ^ 2) := by
  have hC : 0 < ∑ e, 1 / G.adjustedResistance κ e :=
    Finset.sum_pos (fun e _ => one_div_pos.mpr (G.adjustedResistance_pos κ e)) Finset.univ_nonempty
  unfold MetricGraph.resistanceDeficit
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  field_simp [ne_of_gt hC, ne_of_gt G.totalMass_pos, ne_of_gt (G.adjustedResistance_pos κ e)]

omit [Fintype V] in
/-- The variance weights are positive, sum to one, and have the claimed mean. -/
theorem MetricGraph.normalized_resistance_weights (G : MetricGraph V E) (κ : V → ℝ) :
    (∀ e, 0 < 1 / (G.adjustedResistance κ e * ∑ d, 1 / G.adjustedResistance κ d)) ∧
    (∑ e, 1 / (G.adjustedResistance κ e * ∑ d, 1 / G.adjustedResistance κ d)) = 1 ∧
    (∑ e, 1 / (G.adjustedResistance κ e * ∑ d, 1 / G.adjustedResistance κ d) *
      (G.adjustedResistance κ e * G.edgeMass e)) =
        G.totalMass / (∑ d, 1 / G.adjustedResistance κ d) := by
  have hC : 0 < ∑ e, 1 / G.adjustedResistance κ e :=
    Finset.sum_pos (fun e _ => one_div_pos.mpr (G.adjustedResistance_pos κ e)) Finset.univ_nonempty
  refine ⟨fun e => one_div_pos.mpr (mul_pos (G.adjustedResistance_pos κ e) hC), ?_, ?_⟩
  · calc
      _ = (∑ e, 1 / G.adjustedResistance κ e) / (∑ d, 1 / G.adjustedResistance κ d) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _
        field_simp
      _ = 1 := div_self (ne_of_gt hC)
  · calc
      _ = (∑ e, G.edgeMass e) / (∑ d, 1 / G.adjustedResistance κ d) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _
        field_simp [ne_of_gt (G.adjustedResistance_pos κ e)]
      _ = _ := rfl

theorem WeakGraphEquation.reactionDeficit_zero_iff {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.reactionDeficit κ U = 0 ↔ ∀ v, 0 < κ v → U v = G.totalMass / (∑ w, κ w) := by
  have hK : 0 < ∑ v, κ v := by
    obtain ⟨v, hv⟩ := hanchor
    exact Finset.sum_pos' (fun w _ => hκ w) ⟨v, Finset.mem_univ v, hv⟩
  have hid := weighted_variance_identity Finset.univ κ U (ne_of_gt hK) rfl h.conservation
  have heq := (weighted_second_moment_bound Finset.univ κ U hK rfl h.conservation
    (fun v _ => hκ v)).2
  unfold MetricGraph.reactionDeficit
  rw [hid]
  simp only [div_eq_zero_iff, ne_of_gt G.totalMass_pos, or_false, sub_eq_zero]
  simpa only [Finset.mem_univ, forall_const] using heq

theorem WeakGraphEquation.profileDeficit_zero_iff {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.profileDeficit κ u = 0 ↔ ∀ e, G.weakEdgeCost u (G.essentialNorm u) e =
      G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8 := by
  have hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ G.essentialNorm u := by
    intro e x hx
    rw [← h.maximum_eq_essentialNorm hκ hanchor]
    exact h.energy.le_maximum e hx
  have hn := fun e => h.edge_excess_nonneg c hκ hanchor hM e
  unfold MetricGraph.profileDeficit
  simp only [div_eq_zero_iff, ne_of_gt G.totalMass_pos, or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hn e)]
  simp only [Finset.mem_univ, forall_const, sub_eq_zero]

omit [Fintype V] in
theorem MetricGraph.resistanceDeficit_zero_iff (G : MetricGraph V E) (κ : V → ℝ) :
    G.resistanceDeficit κ = 0 ↔ ∀ e, G.adjustedResistance κ e * G.edgeMass e =
      G.totalMass / (∑ d, 1 / G.adjustedResistance κ d) := by
  have hden : (8 : ℝ) * G.totalMass ≠ 0 := ne_of_gt (mul_pos (by positivity) G.totalMass_pos)
  unfold MetricGraph.resistanceDeficit
  simp only [div_eq_zero_iff, hden, or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ =>
    div_nonneg (sq_nonneg _) (G.adjustedResistance_pos κ e).le)]
  simp only [Finset.mem_univ, forall_const]
  apply forall_congr'
  intro e
  simp only [div_eq_zero_iff, ne_of_gt (G.adjustedResistance_pos κ e), or_false,
    sq_eq_zero_iff, sub_eq_zero]

/-- Equality iff there is no reaction variance, no edge-profile excess and
no adjusted-mass imbalance. These are statements about the actual weak state. -/
theorem WeakGraphEquation.sharp_bound_eq_iff {G : MetricGraph V E}
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.essentialNorm u = G.totalMass / (∑ v, κ v) +
      G.totalMass / (8 * ∑ e, 1 / G.adjustedResistance κ e) ↔
      (∀ v, 0 < κ v → U v = G.totalMass / (∑ w, κ w)) ∧
      (∀ e, G.weakEdgeCost u (G.essentialNorm u) e =
        G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8) ∧
      (∀ e, G.adjustedResistance κ e * G.edgeMass e =
        G.totalMass / (∑ d, 1 / G.adjustedResistance κ d)) := by
  rw [← h.reactionDeficit_zero_iff hκ hanchor, ← h.profileDeficit_zero_iff c hκ hanchor,
    ← G.resistanceDeficit_zero_iff κ]
  have hid := h.sharp_deficit_identity hκ hanchor
  obtain ⟨hr, hp, ht⟩ := h.sharp_deficit_nonneg c hκ hanchor
  constructor
  · intro heq
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hrz, hpz, htz⟩
    linarith

end TimeTraps.Graph
