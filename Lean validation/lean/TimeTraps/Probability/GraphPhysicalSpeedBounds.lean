module

public import TimeTraps.Probability.GraphPhysicalSpeed
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! Compactness on each original closed edge and finiteness of the graph
derive uniform positive speed bounds, allowing independent vertex traces. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] in
theorem MetricGraph.source_lower_bound (G : MetricGraph V E) :
    ∃ m : ℝ, 0 < m ∧ ∀ e x, x ∈ Icc 0 (G.length e) → m ≤ G.source e x := by
  classical
  have hedge (e : E) : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc 0 (G.length e), m ≤ G.source e x := by
    obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (0 : ℝ) (G.length e)).Nonempty from ⟨0, le_rfl, (G.length_pos e).le⟩)
      (G.source_continuous e)
    exact ⟨G.source e x, G.source_pos e x hx, hmin⟩
  choose m hm hb using hedge
  obtain ⟨e, _, he⟩ := Finset.exists_min_image Finset.univ m Finset.univ_nonempty
  exact ⟨m e, hm e, fun d x hx => (he d (Finset.mem_univ d)).trans (hb d x hx)⟩

omit [Fintype V] in
theorem MetricGraph.source_upper_bound (G : MetricGraph V E) :
    ∃ M : ℝ, 0 < M ∧ ∀ e x, x ∈ Icc 0 (G.length e) → G.source e x ≤ M := by
  classical
  have hedge (e : E) : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc 0 (G.length e), G.source e x ≤ M := by
    obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (show (Icc (0 : ℝ) (G.length e)).Nonempty from ⟨0, le_rfl, (G.length_pos e).le⟩)
      (G.source_continuous e)
    exact ⟨G.source e x, G.source_pos e x hx, hmax⟩
  choose M hM hb using hedge
  obtain ⟨e, _, he⟩ := Finset.exists_max_image Finset.univ M Finset.univ_nonempty
  exact ⟨M e, hM e, fun d x hx => (hb d x hx).trans (he d (Finset.mem_univ d))⟩

omit [Fintype V] in
theorem MetricGraph.physicalSpeed_bounds (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) :
    ∃ m M : ℝ≥0, 0 < m ∧ ∀ p, (m : ℝ) ≤ G.physicalSpeed b p ∧ G.physicalSpeed b p ≤ (M : ℝ) := by
  obtain ⟨m, hm, hlow⟩ := G.source_lower_bound
  obtain ⟨M, hM, hupp⟩ := G.source_upper_bound
  refine ⟨⟨min b m, (lt_min hb hm).le⟩, ⟨max b M, (hb.trans_le (le_max_left _ _)).le⟩,
    (show (0 : ℝ) < min b m from lt_min hb hm), ?_⟩
  intro p
  rcases G.point_vertex_or_openEdge p with ⟨v, rfl⟩ | ⟨e, x, rfl⟩
  · rw [G.physicalSpeed_vertex]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  · rw [G.physicalSpeed_openEdge]
    exact ⟨(min_le_right _ _).trans (hlow e x.val ⟨x.property.1.le, x.property.2.le⟩),
      (hupp e x.val ⟨x.property.1.le, x.property.2.le⟩).trans (le_max_right _ _)⟩

noncomputable def MetricGraph.physicalSpeedLower (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) : ℝ≥0 :=
  (G.physicalSpeed_bounds b hb).choose

noncomputable def MetricGraph.physicalSpeedUpper (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) : ℝ≥0 :=
  (G.physicalSpeed_bounds b hb).choose_spec.choose

omit [Fintype V] in
theorem MetricGraph.physicalSpeedLower_pos (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) :
    0 < G.physicalSpeedLower b hb :=
  (G.physicalSpeed_bounds b hb).choose_spec.choose_spec.1

omit [Fintype V] in
theorem MetricGraph.physicalSpeed_bound (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphRealization G) :
    (G.physicalSpeedLower b hb : ℝ) ≤ G.physicalSpeed b p ∧
      G.physicalSpeed b p ≤ (G.physicalSpeedUpper b hb : ℝ) :=
  (G.physicalSpeed_bounds b hb).choose_spec.choose_spec.2 p

end TimeTraps.Graph
