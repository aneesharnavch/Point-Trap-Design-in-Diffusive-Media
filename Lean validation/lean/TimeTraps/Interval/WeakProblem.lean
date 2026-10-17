module

public import TimeTraps.Interval.EnergyRestriction

@[expose] public section

/-!
The independent weak equation on the single physical interval. The state and
every test belong to the full interval energy space. The gap construction
proves existence; testing differences proves uniqueness and weak regularity.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

structure WeakIntervalEquation (D : OrderedMedium n) (κ : Fin n → ℝ) (w : ℝ → ℝ) : Prop where
  energy : IntervalEnergy w D.source.left D.source.right
  weak_form : ∀ v, IntervalEnergy v D.source.left D.source.right →
    (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x * deriv v x) +
      (∑ i, κ i * w (D.site i) * v (D.site i)) =
        ∫ x in D.source.left..D.source.right, D.source.density x * v x

theorem WeakIntervalEquation.congr_state {D : OrderedMedium n} {κ : Fin n → ℝ}
    {w z : ℝ → ℝ} (hw : WeakIntervalEquation D κ w)
    (heq : EqOn w z (Icc D.source.left D.source.right)) : WeakIntervalEquation D κ z := by
  refine ⟨hw.energy.congr (by simpa only [uIcc_of_le D.source.increasing.le] using heq), ?_⟩
  intro v hv
  have hd := (heq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have hi : (∫ x in D.source.left..D.source.right, D.conductance x * deriv z x * deriv v x) =
      ∫ x in D.source.left..D.source.right, D.conductance x * deriv w x * deriv v x := by
    apply intervalIntegral.integral_congr_Ioo_of_le D.source.increasing.le
    intro x hx
    dsimp only
    rw [hd hx]
  rw [hi]
  have hs : (∑ i, κ i * z (D.site i) * v (D.site i)) =
      ∑ i, κ i * w (D.site i) * v (D.site i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [heq (Ioo_subset_Icc_self (D.site_interior i))]
  rw [hs]
  exact hw.weak_form v hv

theorem OrderedMedium.assembledState_weak (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    WeakIntervalEquation D κ (D.assembledState U u) := by
  refine ⟨D.assembledState_energy h, ?_⟩
  intro v hv
  have ht := h.to_weak.weak_form (fun k => v (D.node k)) (D.gapRestriction v) (D.restrict_energy hv)
  have ha : ContinuousOn D.conductance (uIcc D.source.left D.source.right) := by
    simpa only [uIcc_of_le D.source.increasing.le] using D.conductance_continuous
  have he : (∑ e, ∫ x in 0..D.graph.length e,
      D.graph.conductance e x * deriv (u e) x * deriv (D.gapRestriction v e) x) =
      ∫ x in D.source.left..D.source.right,
        D.conductance x * deriv (D.assembledState U u) x * deriv v x := by
    rw [← D.integral_gap_sum ((D.assembledState_energy h).bilinear_integrable hv ha)]
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr_Ioo_of_le (D.gapLength_pos e).le
    intro x hx
    change D.conductance (D.node e.castSucc + x) * deriv (u e) x *
      deriv (D.gapRestriction v e) x = _
    dsimp only
    rw [D.gapRestriction_deriv, D.assembledState_gap_deriv h.energy_membership e hx]
  have hs : (∑ e, ∫ x in 0..D.graph.length e, D.graph.source e x * D.gapRestriction v e x) =
      ∫ x in D.source.left..D.source.right, D.source.density x * v x :=
    D.integral_gap_sum (D.source_test_integrable hv)
  have hn : (∑ k, nodalStrength κ k * U k * v (D.node k)) =
      ∑ i, κ i * D.assembledState U u (D.site i) * v (D.site i) := by
    simp_rw [mul_assoc]
    rw [nodalStrength_pairing]
    apply Finset.sum_congr rfl
    intro i _
    change κ i * (U (trapNode i) * v (D.node (trapNode i))) =
      κ i * (D.assembledState U u (D.node (trapNode i)) * v (D.node (trapNode i)))
    rw [D.assembledState_node h.energy_membership]
  rwa [he, hs, hn] at ht

theorem interval_weak_state_exists (D : OrderedMedium n) (κ : Fin n → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) : ∃ w, WeakIntervalEquation D κ w := by
  obtain ⟨U, u, j, h⟩ := graph_state_exists D.graph (nodalStrength κ)
    (nodalStrength_nonneg κ hκ) (nodalStrength_anchor κ hanchor)
  exact ⟨D.assembledState U u, D.assembledState_weak h⟩

theorem WeakIntervalEquation.difference_energy_zero {D : OrderedMedium n} {κ : Fin n → ℝ}
    {w z : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hz : WeakIntervalEquation D κ z) :
    (∫ x in D.source.left..D.source.right,
      D.conductance x * deriv (fun y => w y - z y) x ^ 2) +
      (∑ i, κ i * (w (D.site i) - z (D.site i)) ^ 2) = 0 := by
  let δ : ℝ → ℝ := fun x => w x - z x
  have hδ := hw.energy.sub hz.energy
  have h₁ := hw.weak_form δ hδ
  have h₂ := hz.weak_form δ hδ
  have ha : ContinuousOn D.conductance (uIcc D.source.left D.source.right) := by
    simpa only [uIcc_of_le D.source.increasing.le] using D.conductance_continuous
  have he : (∫ x in D.source.left..D.source.right, D.conductance x * deriv δ x ^ 2) =
      (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x * deriv δ x) -
      (∫ x in D.source.left..D.source.right, D.conductance x * deriv z x * deriv δ x) := by
    simpa only [δ, pow_two, mul_assoc] using hw.energy.bilinear_sub_left hz.energy hδ ha
  have hs : (∑ i, κ i * δ (D.site i) ^ 2) =
      (∑ i, κ i * w (D.site i) * δ (D.site i)) -
      (∑ i, κ i * z (D.site i) * δ (D.site i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [δ]
    ring
  change (∫ x in D.source.left..D.source.right, D.conductance x * deriv δ x ^ 2) +
    (∑ i, κ i * δ (D.site i) ^ 2) = 0
  rw [he, hs]
  linarith

theorem OrderedMedium.energy_zero (D : OrderedMedium n) {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hw : IntervalEnergy w D.source.left D.source.right)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i)
    (hzero : (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x ^ 2) +
      (∑ i, κ i * w (D.site i) ^ 2) = 0) :
    ∀ x ∈ Icc D.source.left D.source.right, w x = 0 := by
  have he : 0 ≤ ∫ x in D.source.left..D.source.right, D.conductance x * deriv w x ^ 2 :=
    intervalIntegral.integral_nonneg D.source.increasing.le
      (fun x hx => mul_nonneg (D.conductance_pos x hx).le (sq_nonneg _))
  have hr : ∀ i, 0 ≤ κ i * w (D.site i) ^ 2 := fun i => mul_nonneg (hκ i) (sq_nonneg _)
  have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hr i)
  have hEz : (∫ x in D.source.left..D.source.right, D.conductance x * deriv w x ^ 2) = 0 := by
    linarith
  have hRz : (∑ i, κ i * w (D.site i) ^ 2) = 0 := by linarith
  have hc := hw.constant_of_energy_zero D.source.increasing.le
    D.conductance_continuous D.conductance_pos hEz
  obtain ⟨i, hi⟩ := hanchor
  have hi₀ := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hr k)).mp hRz i (Finset.mem_univ i)
  have hw₀ : w (D.site i) = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp hi₀).resolve_left (ne_of_gt hi))
  intro x hx
  exact (hc x hx).trans ((hc _ (Ioo_subset_Icc_self (D.site_interior i))).symm.trans hw₀)

theorem interval_weak_state_unique {D : OrderedMedium n} {κ : Fin n → ℝ} {w z : ℝ → ℝ}
    (hw : WeakIntervalEquation D κ w) (hz : WeakIntervalEquation D κ z)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    EqOn w z (Icc D.source.left D.source.right) := by
  have he := D.energy_zero (hw.energy.sub hz.energy) hκ hanchor (hw.difference_energy_zero hz)
  intro x hx
  exact sub_eq_zero.mp (he x hx)

theorem WeakIntervalEquation.to_strong {D : OrderedMedium n} {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    ∃ j, GraphEquation D.graph (nodalStrength κ) (fun v => w (D.node v)) (D.gapRestriction w) j := by
  obtain ⟨U, u, j, h⟩ := graph_state_exists D.graph (nodalStrength κ)
    (nodalStrength_nonneg κ hκ) (nodalStrength_anchor κ hanchor)
  have heq := interval_weak_state_unique hw (D.assembledState_weak h) hκ hanchor
  have hn (v : Fin (n + 2)) : w (D.node v) = U v :=
    (heq (D.node_mem v)).trans (D.assembledState_node h.energy_membership v)
  have hr := D.restrict_energy hw.energy
  refine ⟨j, ⟨?_, hr.tail_value, hr.head_value, ?_⟩⟩
  · intro e
    apply (h.edge_equation e).congr_state
    intro x hx
    exact (heq (D.gap_point_mem e hx)).trans (D.assembledState_gap h.energy_membership e hx)
  · intro v
    rw [hn]
    exact h.vertex_balance v

theorem OrderedMedium.weak_of_strong (D : OrderedMedium n) {κ : Fin n → ℝ} {w : ℝ → ℝ}
    {j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) (fun v => w (D.node v)) (D.gapRestriction w) j) :
    WeakIntervalEquation D κ w := by
  apply (D.assembledState_weak h).congr_state
  intro x hx
  obtain ⟨e, he⟩ := D.gap_cover hx
  have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  simpa only [OrderedMedium.gapRestriction, add_sub_cancel] using D.assembledState_gap h.energy_membership e ht

theorem interval_weak_iff_strong {D : OrderedMedium n} {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    WeakIntervalEquation D κ w ↔
      ∃ j, GraphEquation D.graph (nodalStrength κ) (fun v => w (D.node v)) (D.gapRestriction w) j :=
  ⟨fun h => h.to_strong hκ hanchor, fun ⟨_, h⟩ => D.weak_of_strong h⟩

end TimeTraps.Interval
