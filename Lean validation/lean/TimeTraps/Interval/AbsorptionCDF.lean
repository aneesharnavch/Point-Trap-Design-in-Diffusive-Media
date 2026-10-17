module

public import TimeTraps.Interval.OrderedFlux
public import TimeTraps.Analysis.SourceTransport

@[expose] public section

/-!
The actual absorption-share partition and source-coordinate CDF. Its value
on a gap is proved from the order of the physical sites. The transformed
flux and derivative then follow from the original edge equation.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators Classical

variable {n : ℕ}

theorem absorptionPrefix_strictMono (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    StrictMono (absorptionPrefix p) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [absorptionPrefix_succ]
  exact lt_add_of_pos_right _ (hp i)

theorem absorptionPrefix_div (m : Fin n → ℝ) (S : ℝ) (e : Fin (n + 1)) :
    absorptionPrefix (fun i => m i / S) e = absorptionPrefix m e / S := by
  simp only [absorptionPrefix, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The partition is the cumulative actual absorbed fractions, independently
of the physical site positions. -/
noncomputable def OrderedMedium.absorptionPartition (D : OrderedMedium n)
    (κ : Fin n → ℝ) (U : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  absorptionPrefix (D.absorptionShare κ U)

theorem OrderedMedium.absorptionPartition_first (D : OrderedMedium n)
    (κ : Fin n → ℝ) (U : Fin (n + 2) → ℝ) : D.absorptionPartition κ U 0 = 0 :=
  absorptionPrefix_zero _

theorem OrderedMedium.absorptionPartition_last (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    D.absorptionPartition κ U (Fin.last n) = 1 := by
  rw [OrderedMedium.absorptionPartition, absorptionPrefix_last, D.absorptionShare_sum h]

theorem OrderedMedium.absorptionPartition_strictMono (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (hκ : ∀ i, 0 < κ i) :
    StrictMono (D.absorptionPartition κ U) :=
  absorptionPrefix_strictMono _ (D.absorptionShare_pos h hκ)

theorem OrderedMedium.absorptionPartition_mem (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (hκ : ∀ i, 0 < κ i)
    (e : Fin (n + 1)) : D.absorptionPartition κ U e ∈ Icc (0 : ℝ) 1 := by
  have hm := (D.absorptionPartition_strictMono h hκ).monotone
  constructor
  · simpa only [D.absorptionPartition_first] using hm (Fin.zero_le e)
  · simpa only [D.absorptionPartition_last h] using hm (Fin.le_last e)

noncomputable def OrderedMedium.sourceSite (D : OrderedMedium n) (i : Fin n) : ℝ :=
  D.source.coordinate (D.site i)

noncomputable def OrderedMedium.absorptionCDF (D : OrderedMedium n) (p : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ i, if D.sourceSite i ≤ z then p i else 0

theorem OrderedMedium.site_le_gap_point_iff (D : OrderedMedium n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) (i : Fin n) :
    D.site i ≤ D.node e.castSucc + x ↔ i.val < e.val := by
  have hp : D.node e.castSucc + x < D.node e.succ := by
    have hright := hx.2
    unfold OrderedMedium.gapLength at hright
    linarith
  constructor
  · intro hsite
    have hlt : D.node (trapNode i) < D.node e.succ := hsite.trans_lt hp
    have hi := D.node_strictMono.lt_iff_lt.mp hlt
    change i.val + 1 < e.val + 1 at hi
    omega
  · intro hi
    have hle : trapNode i ≤ e.castSucc := by
      change i.val + 1 ≤ e.val
      omega
    exact (D.node_strictMono.monotone hle).trans (le_add_of_nonneg_right hx.1.le)

theorem OrderedMedium.sourceSite_le_gap_point_iff (D : OrderedMedium n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) (i : Fin n) :
    D.sourceSite i ≤ D.source.coordinate (D.node e.castSucc + x) ↔ i.val < e.val := by
  exact (D.source.coordinate_strictMono.le_iff_le
    (Ioo_subset_Icc_self (D.site_interior i)) (D.gap_point_mem e (Ioo_subset_Icc_self hx))).trans
      (D.site_le_gap_point_iff e hx i)

theorem OrderedMedium.absorptionCDF_gap (D : OrderedMedium n) (p : Fin n → ℝ)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo 0 (D.gapLength e)) :
    D.absorptionCDF p (D.source.coordinate (D.node e.castSucc + x)) = absorptionPrefix p e := by
  unfold OrderedMedium.absorptionCDF absorptionPrefix
  apply Finset.sum_congr rfl
  intro i _
  simp only [D.sourceSite_le_gap_point_iff e hx i]

/-- The paper's source-coordinate flux law, for actual physical gap states. -/
theorem OrderedMedium.absorption_flux (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) :
    j e x = D.source.mass *
      (D.absorptionCDF (D.absorptionShare κ U) (D.source.coordinate (D.node e.castSucc + x)) -
        D.source.coordinate (D.node e.castSucc + x)) := by
  rw [D.absorptionCDF_gap _ e hx, D.gap_flux h e (Ioo_subset_Icc_self hx)]
  change absorptionPrefix (fun i => κ i * U (trapNode i)) e - _ =
    D.source.mass * (absorptionPrefix (fun i => (κ i * U (trapNode i)) / D.source.mass) e - _)
  rw [absorptionPrefix_div]
  field_simp [ne_of_gt D.source.mass_pos]

noncomputable def OrderedMedium.transformedGapState (D : OrderedMedium n)
    (u : Fin (n + 1) → ℝ → ℝ) (e : Fin (n + 1)) (z : ℝ) : ℝ :=
  u e (D.source.inverse z - D.node e.castSucc)

/-- Differentiation of the actual physical state, after applying the global
source inverse. The point lies strictly inside the specified physical gap. -/
theorem OrderedMedium.transformed_gap_derivative (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (e : Fin (n + 1)) {z : ℝ}
    (hz : z ∈ Ioo 0 1)
    (hx : D.source.inverse z - D.node e.castSucc ∈ Ioo 0 (D.gapLength e)) :
    HasDerivAt (D.transformedGapState u e)
      (D.source.weight D.conductance z * (D.absorptionCDF (D.absorptionShare κ U) z - z)) z := by
  have hd := ((h.edge_equation e).state_derivative _ hx).comp z
    ((D.source.inverse_derivative hz).sub_const (D.node e.castSucc))
  have hf := D.absorption_flux h e hx
  have hpoint : D.node e.castSucc + (D.source.inverse z - D.node e.castSucc) = D.source.inverse z := by
    ring
  rw [hpoint, D.source.coordinate_inverse (Ioo_subset_Icc_self hz)] at hf
  change HasDerivAt (D.transformedGapState u e)
    ((j e (D.source.inverse z - D.node e.castSucc) /
      D.conductance (D.node e.castSucc + (D.source.inverse z - D.node e.castSucc))) *
        (D.source.mass / D.source.density (D.source.inverse z))) z at hd
  rw [hf, hpoint] at hd
  convert hd using 1
  unfold SourceInterval.weight
  field_simp [ne_of_gt (D.conductance_pos _ (D.source.inverse_mem z)),
    ne_of_gt (D.source.positive _ (D.source.inverse_mem z))]

/-- The flux law applies to every ordered-path weak state by the independently
proved weak/strong equivalence; no CDF identity is a premise. -/
theorem OrderedMedium.weak_absorption_flux (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (h : WeakGraphEquation D.graph (nodalStrength κ) U u)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    ∃ j, GraphEquation D.graph (nodalStrength κ) U u j ∧
      ∀ e x, x ∈ Ioo 0 (D.gapLength e) →
        j e x = D.source.mass *
          (D.absorptionCDF (D.absorptionShare κ U) (D.source.coordinate (D.node e.castSucc + x)) -
            D.source.coordinate (D.node e.castSucc + x)) := by
  obtain ⟨j, hj⟩ := h.to_strong (nodalStrength_nonneg κ hκ) (nodalStrength_anchor κ hanchor)
  exact ⟨j, hj, fun e _ hx => D.absorption_flux hj e hx⟩

end TimeTraps.Interval
