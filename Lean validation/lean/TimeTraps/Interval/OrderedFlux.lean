module

public import TimeTraps.Interval.OrderedDesign

@[expose] public section

/-!
Source conservation and the cumulative absorption law for the ordered
physical gaps. The prefix flux is derived by induction from the reflecting
left end, the differential equation, and the reaction jumps.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

def absorptionPrefix (m : Fin n → ℝ) (e : Fin (n + 1)) : ℝ :=
  ∑ i, if i.val < e.val then m i else 0

theorem absorptionPrefix_zero (m : Fin n → ℝ) : absorptionPrefix m 0 = 0 := by
  simp [absorptionPrefix]

theorem absorptionPrefix_succ (m : Fin n → ℝ) (i : Fin n) :
    absorptionPrefix m i.succ = absorptionPrefix m i.castSucc + m i := by
  have hi : ∀ k : Fin n, (if k.val < i.succ.val then m k else 0) =
      (if k.val < i.castSucc.val then m k else 0) + (if k = i then m k else 0) := by
    intro k
    by_cases hlt : k.val < i.val
    · have hne : k ≠ i := by intro he; subst k; omega
      simp [hlt, hne, show k.val < i.val + 1 by omega]
    · by_cases he : k = i
      · subst k
        simp
      · have hn : ¬ k.val < i.val + 1 := by
          have hv : k.val ≠ i.val := fun h => he (Fin.ext h)
          omega
        simp [hlt, he, hn]
  unfold absorptionPrefix
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp

theorem absorptionPrefix_last (m : Fin n → ℝ) : absorptionPrefix m (Fin.last n) = ∑ i, m i := by
  simp [absorptionPrefix]

theorem fin_sum_adjacent_difference (A : Fin (n + 2) → ℝ) :
    (∑ e : Fin (n + 1), (A e.succ - A e.castSucc)) = A (Fin.last (n + 1)) - A 0 := by
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ A
  have h₁ := Fin.sum_univ_castSucc A
  linarith

theorem OrderedMedium.gap_source_primitive (D : OrderedMedium n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc 0 (D.gapLength e)) :
    sourcePrimitive (D.graph.source e) 0 x = D.source.mass *
      (D.source.coordinate (D.node e.castSucc + x) - D.source.coordinate (D.node e.castSucc)) := by
  change (∫ t in 0..x, D.source.density (D.node e.castSucc + t)) = _
  rw [intervalIntegral.integral_comp_add_left, add_zero]
  exact D.source.mass_fraction (D.node_mem e.castSucc) (D.gap_point_mem e hx)
    (le_add_of_nonneg_right hx.1)

theorem OrderedMedium.gap_source_mass (D : OrderedMedium n) (e : Fin (n + 1)) :
    sourcePrimitive (D.graph.source e) 0 (D.gapLength e) = D.source.mass *
      (D.source.coordinate (D.node e.succ) - D.source.coordinate (D.node e.castSucc)) := by
  simpa only [OrderedMedium.gapLength, add_sub_cancel] using
    D.gap_source_primitive e ⟨(D.gapLength_pos e).le, le_rfl⟩

theorem OrderedMedium.graph_mass (D : OrderedMedium n) : D.graph.totalMass = D.source.mass := by
  change (∑ e, sourcePrimitive (D.graph.source e) 0 (D.gapLength e)) = _
  simp_rw [D.gap_source_mass]
  rw [← Finset.mul_sum, fin_sum_adjacent_difference (fun v => D.source.coordinate (D.node v))]
  rw [D.node_first, D.node_last, D.source.coordinate_left, D.source.coordinate_right]
  ring

theorem OrderedMedium.source_conservation (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    (∑ i, κ i * U (trapNode i)) = D.source.mass := by
  rw [← nodalStrength_pairing, ← D.graph_mass]
  exact h.conservation

theorem OrderedMedium.initial_gap_flux (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (e : Fin (n + 1)) :
    j e 0 = absorptionPrefix (fun i => κ i * U (trapNode i)) e -
      D.source.mass * D.source.coordinate (D.node e.castSucc) := by
  induction e using Fin.induction with
  | zero =>
    simpa only [absorptionPrefix_zero, Fin.castSucc_zero, D.node_first,
      D.source.coordinate_left, mul_zero, sub_zero] using (D.reflecting_endpoints h).1
  | succ i ih =>
    have hf := (h.edge_equation i.castSucc).flux_formula (D.graph.source_continuous i.castSucc)
      (show D.gapLength i.castSucc ∈ Icc 0 (D.graph.length i.castSucc) from
        ⟨(D.gapLength_pos i.castSucc).le, le_rfl⟩)
    rw [D.gap_source_mass, ih] at hf
    have hj := D.flux_jump h i
    rw [absorptionPrefix_succ]
    change j i.succ 0 = absorptionPrefix (fun k => κ k * U (trapNode k)) i.castSucc +
      κ i * U (trapNode i) - D.source.mass * D.source.coordinate (D.node i.castSucc.succ)
    linarith

/-- The exact physical flux at every point of a closed gap. At a trap, the
two neighboring gap representatives give its two one-sided fluxes. -/
theorem OrderedMedium.gap_flux (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc 0 (D.gapLength e)) :
    j e x = absorptionPrefix (fun i => κ i * U (trapNode i)) e -
      D.source.mass * D.source.coordinate (D.node e.castSucc + x) := by
  have hf := (h.edge_equation e).flux_formula (D.graph.source_continuous e) hx
  rw [D.initial_gap_flux h e, D.gap_source_primitive e hx] at hf
  linarith

noncomputable def OrderedMedium.absorptionShare (D : OrderedMedium n)
    (κ : Fin n → ℝ) (U : Fin (n + 2) → ℝ) (i : Fin n) : ℝ :=
  κ i * U (trapNode i) / D.source.mass

theorem OrderedMedium.absorptionShare_sum (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) : ∑ i, D.absorptionShare κ U i = 1 := by
  simp only [OrderedMedium.absorptionShare, ← Finset.sum_div, D.source_conservation h,
    div_self (ne_of_gt D.source.mass_pos)]

theorem OrderedMedium.absorptionShare_pos (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    0 < D.absorptionShare κ U i := by
  have hU := (h.positive (nodalStrength_nonneg κ (fun i => (hκ i).le))).1
  exact div_pos (mul_pos (hκ i) (hU (trapNode i))) D.source.mass_pos

end TimeTraps.Interval
