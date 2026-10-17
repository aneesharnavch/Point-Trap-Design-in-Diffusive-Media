module

public import TimeTraps.Interval.StateAssembly
public import TimeTraps.Graph.StateMaximum

@[expose] public section

/-!
Global physical representatives of ordered-path states, their positivity and
attained maximum, and the source-coordinate derivative away from traps.
The remaining global H1 weak-equation identification is a separate obligation.
-/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Graph
open scoped Topology

variable {n : ℕ}

theorem OrderedMedium.gap_cover (D : OrderedMedium n) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    ∃ e : Fin (n + 1), x ∈ Icc (D.node e.castSucc) (D.node e.succ) := by
  have hc : ∀ e : Fin (n + 1), ∀ y ∈ Icc (D.node 0) (D.node e.succ),
      ∃ d : Fin (n + 1), y ∈ Icc (D.node d.castSucc) (D.node d.succ) := by
    intro e
    induction e using Fin.induction with
    | zero =>
      intro y hy
      exact ⟨0, hy⟩
    | succ i ih =>
      intro y hy
      by_cases hb : y ≤ D.node i.castSucc.succ
      · exact ih y ⟨hy.1, hb⟩
      · exact ⟨i.succ, ⟨(lt_of_not_ge hb).le, hy.2⟩⟩
  apply hc (Fin.last n) x
  change x ∈ Icc (D.node 0) (D.node (Fin.last (n + 1)))
  simpa only [D.node_first, D.node_last] using hx

theorem OrderedMedium.gap_cover_open (D : OrderedMedium n) {x : ℝ}
    (hx : x ∈ Ioo D.source.left D.source.right) (hsite : ∀ i, D.site i ≠ x) :
    ∃ e : Fin (n + 1), x ∈ Ioo (D.node e.castSucc) (D.node e.succ) := by
  have hn : ∀ v : Fin (n + 2), D.node v ≠ x := by
    intro v
    refine Fin.cases ?_ (fun w => ?_) v
    · rw [D.node_first]
      exact ne_of_lt hx.1
    · refine Fin.lastCases ?_ (fun i => ?_) w
      · change D.node (Fin.last (n + 1)) ≠ x
        rw [D.node_last]
        exact ne_of_gt hx.2
      · exact hsite i
  obtain ⟨e, he⟩ := D.gap_cover (Ioo_subset_Icc_self hx)
  exact ⟨e, ⟨lt_of_le_of_ne he.1 (hn e.castSucc), lt_of_le_of_ne he.2 (hn e.succ).symm⟩⟩

theorem OrderedMedium.assembledState_positive (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (hκ : ∀ i, 0 ≤ κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) : 0 < D.assembledState U u x := by
  obtain ⟨e, he⟩ := D.gap_cover hx
  have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) := by
    exact ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  have hid : D.assembledState U u x = u e (x - D.node e.castSucc) := by
    simpa only [add_sub_cancel] using D.assembledState_gap h.energy_membership e ht
  rw [hid]
  exact (h.positive (nodalStrength_nonneg κ hκ)).2 e _ ht

theorem OrderedMedium.assembledState_values (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u) :
    D.assembledState U u '' Icc D.source.left D.source.right = D.graph.stateValues u := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := D.gap_cover hx
    have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) :=
      ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
    apply mem_iUnion.mpr
    refine ⟨e, x - D.node e.castSucc, ht, ?_⟩
    have hid : D.assembledState U u x = u e (x - D.node e.castSucc) := by
      simpa only [add_sub_cancel] using D.assembledState_gap h e ht
    exact hid.symm
  · intro hy
    obtain ⟨e, x, hx, rfl⟩ := mem_iUnion.mp hy
    exact ⟨D.node e.castSucc + x, D.gap_point_mem e hx, D.assembledState_gap h e hx⟩

theorem OrderedMedium.assembledState_maximum (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u) :
    IsGreatest (D.assembledState U u '' Icc D.source.left D.source.right) (D.graph.stateMaximum u) := by
  rw [D.assembledState_values h]
  exact h.maximum_isGreatest

/-- The same attained physical state, now as a single function of normalized
source coordinate. The inverse is extended constantly outside [0,1]. -/
noncomputable def OrderedMedium.transformedState (D : OrderedMedium n)
    (U : Fin (n + 2) → ℝ) (u : Fin (n + 1) → ℝ → ℝ) : ℝ → ℝ :=
  D.source.transformed (D.assembledState U u)

theorem OrderedMedium.transformedState_continuous (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u) :
    Continuous (D.transformedState U u) :=
  D.source.transformed_continuous (D.assembledState_continuous h).continuousOn

theorem OrderedMedium.transformedState_site (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u)
    (i : Fin n) : D.transformedState U u (D.sourceSite i) = U (trapNode i) := by
  change D.source.transformed (D.assembledState U u) (D.source.coordinate (D.site i)) = _
  rw [D.source.transformed_coordinate _ (Ioo_subset_Icc_self (D.site_interior i))]
  exact D.assembledState_node h (trapNode i)

theorem OrderedMedium.transformedState_values (D : OrderedMedium n)
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ} (h : GraphEnergy D.graph U u) :
    D.transformedState U u '' Icc (0 : ℝ) 1 = D.graph.stateValues u := by
  rw [← D.assembledState_values h]
  ext y
  constructor
  · rintro ⟨z, _, rfl⟩
    exact ⟨D.source.inverse z, D.source.inverse_mem z, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨D.source.coordinate x, D.source.coordinate_mem hx,
      D.source.transformed_coordinate _ hx⟩

theorem OrderedMedium.transformedState_derivative (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) {z : ℝ}
    (hz : z ∈ Ioo 0 1) (hsite : ∀ i, D.sourceSite i ≠ z) :
    HasDerivAt (D.transformedState U u)
      (D.source.weight D.conductance z * (D.absorptionCDF (D.absorptionShare κ U) z - z)) z := by
  have hn : ∀ i, D.site i ≠ D.source.inverse z := by
    intro i he
    apply hsite i
    change D.source.coordinate (D.site i) = z
    rw [he, D.source.coordinate_inverse (Ioo_subset_Icc_self hz)]
  obtain ⟨e, he⟩ := D.gap_cover_open (D.source.inverse_interior hz) hn
  have ht : D.source.inverse z - D.node e.castSucc ∈ Ioo 0 (D.gapLength e) :=
    ⟨sub_pos.mpr he.1, sub_lt_sub_right he.2 _⟩
  have heq := (D.assembledState_eventually_gap h.energy_membership e he).comp_tendsto
    D.source.inverse_continuous.continuousAt
  exact (D.transformed_gap_derivative h e hz ht).congr_of_eventuallyEq heq

theorem OrderedMedium.weak_transformedState_derivative (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (h : WeakGraphEquation D.graph (nodalStrength κ) U u)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) {z : ℝ}
    (hz : z ∈ Ioo 0 1) (hsite : ∀ i, D.sourceSite i ≠ z) :
    HasDerivAt (D.transformedState U u)
      (D.source.weight D.conductance z * (D.absorptionCDF (D.absorptionShare κ U) z - z)) z := by
  obtain ⟨j, hj⟩ := h.to_strong (nodalStrength_nonneg κ hκ) (nodalStrength_anchor κ hanchor)
  exact D.transformedState_derivative hj hz hsite

end TimeTraps.Interval
