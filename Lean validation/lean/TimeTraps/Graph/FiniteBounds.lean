module

public import TimeTraps.Analysis.WeightedVariance
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
Finite inequalities and the exact deficit decomposition used by the graph
theorem. Here `t e = χ_e r_e`. Conservation, edge barriers, and the energy
identity are explicit premises: this module does not claim to supply the
metric-graph weak-solution bridge or its equality reconstruction.
-/

namespace TimeTraps.Graph

open scoped BigOperators

variable {E Vtx : Type*} [Fintype E] [Fintype Vtx]

/-- The weighted edge imbalance is exactly the gap in mass--resistance Cauchy--Schwarz. -/
theorem mass_resistance_variance (t m : E → ℝ) (ht : ∀ e, 0 < t e)
    {V C : ℝ} (hC : C ≠ 0) (hm : ∑ e, m e = V) (hc : ∑ e, 1 / t e = C) :
    (∑ e, (t e * m e - V / C) ^ 2 / t e) =
      (∑ e, t e * m e ^ 2) - V ^ 2 / C := by
  have hfirst : (∑ e, (1 / t e) * (t e * m e)) = V := by
    convert hm using 1
    apply Finset.sum_congr rfl
    intro e _
    field_simp [ne_of_gt (ht e)]
  have hsecond : (∑ e, (1 / t e) * (t e * m e) ^ 2) = ∑ e, t e * m e ^ 2 := by
    apply Finset.sum_congr rfl
    intro e _
    field_simp [ne_of_gt (ht e)]
  have hid := TimeTraps.Analysis.weighted_variance_identity Finset.univ
    (fun e => 1 / t e) (fun e => t e * m e) hC hc hfirst
  rw [hsecond] at hid
  simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hid

theorem mass_resistance_bound (t m : E → ℝ) (ht : ∀ e, 0 < t e)
    {V C : ℝ} (hC : 0 < C) (hm : ∑ e, m e = V) (hc : ∑ e, 1 / t e = C) :
    V ^ 2 / C ≤ (∑ e, t e * m e ^ 2) ∧
      ((∑ e, t e * m e ^ 2) = V ^ 2 / C ↔ ∀ e, t e * m e = V / C) := by
  have hid := mass_resistance_variance t m ht (ne_of_gt hC) hm hc
  have hn : ∀ e, 0 ≤ (t e * m e - V / C) ^ 2 / t e :=
    fun e => div_nonneg (sq_nonneg _) (ht e).le
  have hsum := Finset.sum_nonneg (fun e (_ : e ∈ Finset.univ) => hn e)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h e
    have hz : (∑ e, (t e * m e - V / C) ^ 2 / t e) = 0 := by linarith
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hn e)).mp hz e (Finset.mem_univ e)
    have hsq : (t e * m e - V / C) ^ 2 = 0 :=
      (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (ht e))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro h
    have hz : (∑ e, (t e * m e - V / C) ^ 2 / t e) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [h e, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div]
    linarith

/-- Both graph inequalities as finite consequences of conservation and the
edge and energy identities. All premises that still need a graph bridge are visible. -/
theorem finite_graph_bounds (κ u : Vtx → ℝ) (t m J : E → ℝ)
    {V K C M : ℝ} (hV : 0 < V) (hK : 0 < K) (hC : 0 < C)
    (hκ : ∀ v, 0 ≤ κ v) (ht : ∀ e, 0 < t e)
    (hk : ∑ v, κ v = K) (hcons : ∑ v, κ v * u v = V)
    (hm : ∑ e, m e = V) (hc : ∑ e, 1 / t e = C)
    (hedge : ∀ e, t e * m e ^ 2 / 8 ≤ J e)
    (henergy : V * M = (∑ v, κ v * u v ^ 2) + ∑ e, J e) :
    V / K + (∑ e, t e * m e ^ 2) / (8 * V) ≤ M ∧
      V / K + V / (8 * C) ≤ V / K + (∑ e, t e * m e ^ 2) / (8 * V) := by
  have hr := (TimeTraps.Analysis.weighted_second_moment_bound
    Finset.univ κ u hK hk hcons (fun v _ => hκ v)).1
  have he : (∑ e, t e * m e ^ 2) / 8 ≤ ∑ e, J e := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun e _ => hedge e
  have hmass := (mass_resistance_bound t m ht hC hm hc).1
  constructor
  · apply (mul_le_mul_iff_right₀ hV).mp
    have hform : V * (V / K + (∑ e, t e * m e ^ 2) / (8 * V)) =
        V ^ 2 / K + (∑ e, t e * m e ^ 2) / 8 := by field_simp
    rw [hform, henergy]
    linarith
  · apply add_le_add le_rfl
    have hdiv := div_le_div_of_nonneg_right hmass (by positivity : 0 ≤ 8 * V)
    have hform : (V ^ 2 / C) / (8 * V) = V / (8 * C) := by field_simp
    rwa [hform] at hdiv

/-- An exact three-term deficit formula in weighted-square form. -/
theorem finite_graph_deficit (κ u : Vtx → ℝ) (t m J : E → ℝ)
    {V K C M : ℝ} (hV : V ≠ 0) (hK : K ≠ 0) (hC : C ≠ 0)
    (ht : ∀ e, 0 < t e)
    (hk : ∑ v, κ v = K) (hcons : ∑ v, κ v * u v = V)
    (hm : ∑ e, m e = V) (hc : ∑ e, 1 / t e = C)
    (henergy : V * M = (∑ v, κ v * u v ^ 2) + ∑ e, J e) :
    M - V / K - V / (8 * C) =
      (∑ v, κ v * (u v - V / K) ^ 2) / V +
      (∑ e, (J e - t e * m e ^ 2 / 8)) / V +
      (∑ e, (t e * m e - V / C) ^ 2 / t e) / (8 * V) := by
  rw [TimeTraps.Analysis.weighted_variance_identity Finset.univ κ u hK hk hcons,
    mass_resistance_variance t m ht hC hm hc,
    Finset.sum_sub_distrib, ← Finset.sum_div]
  have hM : M = ((∑ v, κ v * u v ^ 2) + ∑ e, J e) / V := by
    apply (eq_div_iff hV).mpr
    linarith
  rw [hM]
  field_simp
  ring

/-- The reaction variance equals the manuscript's absorption-share pair term.
The double sum is divided by two instead of choosing an ordering of vertices. -/
theorem reaction_deficit_pairwise (κ u : Vtx → ℝ) {V K : ℝ}
    (hV : V ≠ 0) (hK : K ≠ 0) (hu : ∀ v, u v ≠ 0)
    (hk : ∑ v, κ v = K) (hcons : ∑ v, κ v * u v = V) :
    (∑ v, κ v * (u v - V / K) ^ 2) / V =
      V / K * ((1 / 2 : ℝ) * ∑ v, ∑ w,
        (κ v * u v / V) * (κ w * u w / V) * (u v - u w) ^ 2 / (u v * u w)) := by
  have hnorm : (∑ v, ∑ w,
      (κ v * u v / V) * (κ w * u w / V) * (u v - u w) ^ 2 / (u v * u w)) =
      (∑ v, ∑ w, κ v * κ w * (u v - u w) ^ 2) / V ^ 2 := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    field_simp [hu v, hu w]
  rw [TimeTraps.Analysis.weighted_variance_identity Finset.univ κ u hK hk hcons,
    hnorm, TimeTraps.Analysis.weighted_pairwise_identity, hk, hcons]
  field_simp

/-- The paper's normalized variance form of the finite deficit identity. -/
theorem finite_graph_deficit_normalized (κ u : Vtx → ℝ) (t m J : E → ℝ)
    {V K C M : ℝ} (hV : V ≠ 0) (hK : K ≠ 0) (hC : C ≠ 0)
    (hu : ∀ v, u v ≠ 0) (ht : ∀ e, 0 < t e)
    (hk : ∑ v, κ v = K) (hcons : ∑ v, κ v * u v = V)
    (hm : ∑ e, m e = V) (hc : ∑ e, 1 / t e = C)
    (henergy : V * M = (∑ v, κ v * u v ^ 2) + ∑ e, J e) :
    M - V / K - V / (8 * C) =
      V / K * ((1 / 2 : ℝ) * ∑ v, ∑ w,
        (κ v * u v / V) * (κ w * u w / V) * (u v - u w) ^ 2 / (u v * u w)) +
      (∑ e, (J e - t e * m e ^ 2 / 8)) / V +
      C / (8 * V) * (∑ e, 1 / (t e * C) * (t e * m e - V / C) ^ 2) := by
  rw [finite_graph_deficit κ u t m J hV hK hC ht hk hcons hm hc henergy,
    reaction_deficit_pairwise κ u hV hK hu hk hcons]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  field_simp [ne_of_gt (ht e)]

end TimeTraps.Graph
