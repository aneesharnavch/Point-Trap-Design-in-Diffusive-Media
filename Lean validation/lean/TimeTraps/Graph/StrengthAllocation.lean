module

public import TimeTraps.Graph.SharpEquality

@[expose] public section

/-!
Construct reactivities of any positive budget from the equality flux loads.
The input marker selects passive leaves; its other values are immaterial.
Preservation of the passive leaves and the exact budget are proved, so the
construction does not assume its own reactivity classification.
-/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.allocatedStrength (G : MetricGraph V E)
    (marker : V → ℝ) (K : ℝ) (v : V) : ℝ := K / G.totalMass * G.sharpLoad marker v

omit [Fintype V] in
theorem MetricGraph.allocatedStrength_nonneg (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 ≤ K) (v : V) :
    0 ≤ G.allocatedStrength marker K v := by
  unfold MetricGraph.allocatedStrength MetricGraph.sharpLoad
  split_ifs
  · simp
  · exact mul_nonneg (div_nonneg hK G.totalMass_pos.le) (G.coreLoad_pos marker v).le

omit [Fintype V] in
theorem MetricGraph.allocatedStrength_pos_iff (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K) (v : V) :
    0 < G.allocatedStrength marker K v ↔ ¬G.IsPassiveTip marker v := by
  by_cases hp : G.IsPassiveTip marker v
  · simp [MetricGraph.allocatedStrength, MetricGraph.sharpLoad, hp]
  · have hpos : 0 < G.allocatedStrength marker K v := by
      unfold MetricGraph.allocatedStrength MetricGraph.sharpLoad
      rw [if_neg hp]
      exact mul_pos (div_pos hK G.totalMass_pos) (G.coreLoad_pos marker v)
    exact ⟨fun _ => hp, fun _ => hpos⟩

omit [Fintype V] in
theorem MetricGraph.allocatedStrength_passive_iff (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K) (v : V) :
    G.IsPassiveTip (G.allocatedStrength marker K) v ↔ G.IsPassiveTip marker v := by
  constructor
  · intro hv
    by_contra hp
    exact (ne_of_gt ((G.allocatedStrength_pos_iff marker hK v).mpr hp)) hv.1
  · intro hp
    refine ⟨?_, hp.2⟩
    simp [MetricGraph.allocatedStrength, MetricGraph.sharpLoad, hp]

theorem MetricGraph.allocatedStrength_sum (G : MetricGraph V E)
    (marker : V → ℝ) (K : ℝ)
    (hno : ∀ e, ¬(G.IsPassiveTip marker (G.tail e) ∧ G.IsPassiveTip marker (G.head e))) :
    ∑ v, G.allocatedStrength marker K v = K := by
  simp only [MetricGraph.allocatedStrength]
  rw [← Finset.mul_sum, G.sharpLoad_sum marker hno]
  exact div_mul_cancel₀ K (ne_of_gt G.totalMass_pos)

theorem MetricGraph.allocatedStrength_anchor (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K)
    (hno : ∀ e, ¬(G.IsPassiveTip marker (G.tail e) ∧ G.IsPassiveTip marker (G.head e))) :
    ∃ v, 0 < G.allocatedStrength marker K v := by
  by_contra hn
  push Not at hn
  have hs := Finset.sum_nonpos (s := Finset.univ) (fun v _ => hn v)
  rw [G.allocatedStrength_sum marker K hno] at hs
  linarith

omit [Fintype V] in
theorem MetricGraph.allocatedStrength_reflection (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K) (e : E) :
    G.reflectionFactor (G.allocatedStrength marker K) e = G.reflectionFactor marker e := by
  simp only [MetricGraph.reflectionFactor, G.allocatedStrength_passive_iff marker hK]

omit [Fintype V] in
theorem MetricGraph.allocatedStrength_resistance (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K) (e : E) :
    G.adjustedResistance (G.allocatedStrength marker K) e = G.adjustedResistance marker e := by
  simp only [MetricGraph.adjustedResistance, G.allocatedStrength_reflection marker hK]

omit [Fintype V] in
theorem MetricGraph.allocatedStrength_coreLoad (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K) (v : V) :
    G.coreLoad (G.allocatedStrength marker K) v = G.coreLoad marker v := by
  have hs : G.edgeShare (G.allocatedStrength marker K) = G.edgeShare marker := by
    funext e
    simp only [MetricGraph.edgeShare, G.allocatedStrength_reflection marker hK]
  simp only [MetricGraph.coreLoad, hs]

theorem MetricGraph.allocatedStrength_sharp (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K)
    (hno : ∀ e, ¬(G.IsPassiveTip marker (G.tail e) ∧ G.IsPassiveTip marker (G.head e))) :
    G.HasSharpStrengths (G.allocatedStrength marker K) := by
  intro v hv
  have hp : ¬G.IsPassiveTip marker v := fun hp =>
    hv ((G.allocatedStrength_passive_iff marker hK v).mpr hp)
  rw [G.allocatedStrength_sum marker K hno, G.allocatedStrength_coreLoad marker hK v]
  simp [MetricGraph.allocatedStrength, MetricGraph.sharpLoad, hp]

omit [Fintype V] in
theorem MetricGraph.allocatedStrength_balanced (G : MetricGraph V E)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K) (hbal : G.HasBalancedMasses marker) :
    G.HasBalancedMasses (G.allocatedStrength marker K) := by
  intro e
  simpa only [G.allocatedStrength_resistance marker hK] using hbal e

/-- Every balanced geometry with the chosen passive leaves has an explicitly
constructed attaining design of any positive total reaction budget. -/
theorem MetricGraph.allocated_design_attains (G : MetricGraph V E) (c : EdgeConstants G)
    (marker : V → ℝ) {K : ℝ} (hK : 0 < K)
    (hno : ∀ e, ¬(G.IsPassiveTip marker (G.tail e) ∧ G.IsPassiveTip marker (G.head e)))
    (hbal : G.HasBalancedMasses marker) :
    (∑ v, G.allocatedStrength marker K v) = K ∧
      ∃ U u, WeakGraphEquation G (G.allocatedStrength marker K) U u ∧
        G.essentialNorm u = G.totalMass / K +
          G.totalMass / (8 * ∑ e, 1 / G.adjustedResistance marker e) := by
  refine ⟨G.allocatedStrength_sum marker K hno, ?_⟩
  have hκ := G.allocatedStrength_nonneg marker hK.le
  have ha := G.allocatedStrength_anchor marker hK hno
  obtain ⟨hw, hm⟩ := G.sharp_profile_attains c (G.allocatedStrength marker K) hκ ha
    (G.allocatedStrength_balanced marker hK hbal) (G.allocatedStrength_sharp marker hK hno)
  refine ⟨_, _, hw, ?_⟩
  rw [hm, MetricGraph.boundHeight, G.allocatedStrength_sum marker K hno]
  simp only [G.allocatedStrength_resistance marker hK]

end TimeTraps.Graph
