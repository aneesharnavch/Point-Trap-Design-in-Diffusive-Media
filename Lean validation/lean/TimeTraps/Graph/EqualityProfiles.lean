module

public import TimeTraps.Graph.SharpDeficit

@[expose] public section

/-!
Geometric equality profiles and their endpoint fluxes. The peak location is
defined from passive-tip incidence, independently of any state or optimizer.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*}

noncomputable def MetricGraph.peakPosition (G : MetricGraph V E) (κ : V → ℝ) (e : E) : ℝ := by
  classical
  exact if G.IsPassiveTip κ (G.tail e) then 0 else
    if G.IsPassiveTip κ (G.head e) then G.length e else G.length e / 2

noncomputable def EdgeConstants.sharpProfile {G : MetricGraph V E} (c : EdgeConstants G)
    (κ : V → ℝ) (M : ℝ) (e : E) (x : ℝ) : ℝ :=
  M - c.source e / (2 * c.conductance e) * (x - G.peakPosition κ e) ^ 2

noncomputable def EdgeConstants.sharpFlux {G : MetricGraph V E} (c : EdgeConstants G)
    (κ : V → ℝ) (e : E) (x : ℝ) : ℝ :=
  c.source e * (G.peakPosition κ e - x)

/-- A positive source forbids an edge with zero flux at both ends. -/
theorem GraphEquation.not_two_passive_tips [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (e : E) :
    ¬(G.IsPassiveTip κ (G.tail e) ∧ G.IsPassiveTip κ (G.head e)) := by
  rintro ⟨ht, hh⟩
  have ha := (h.edge_equation e).flux_strictAntiOn
    (fun x hx => G.source_pos e x ⟨hx.1.le, hx.2.le⟩)
    ⟨le_rfl, (G.length_pos e).le⟩ ⟨(G.length_pos e).le, le_rfl⟩ (G.length_pos e)
  rw [h.passive_tail_neumann ht, h.passive_head_neumann hh] at ha
  exact (lt_irrefl 0) ha

theorem MetricGraph.peakPosition_mem (G : MetricGraph V E) (κ : V → ℝ) (e : E) :
    G.peakPosition κ e ∈ Icc 0 (G.length e) := by
  unfold MetricGraph.peakPosition
  split_ifs <;> constructor <;> linarith [G.length_pos e]

/-- Exact vanishing conditions for the local edge cost, with either orientation
of a passive tip handled by the same independently defined peak position. -/
theorem GraphEquation.sharp_edge_parameters [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j)
    (c : EdgeConstants G) (M : ℝ) (e : E)
    (hM : ∀ x ∈ Icc 0 (G.length e), u e x ≤ M) :
    G.weakEdgeCost u M e = G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8 ↔
      j e 0 / c.source e = G.peakPosition κ e ∧
      M - u e 0 - j e 0 ^ 2 / (2 * c.conductance e * c.source e) = 0 := by
  classical
  have he := constant_edge_of_eqOn (h.edge_equation e) (c.conductance_eq e) (c.source_eq e)
  rw [h.weakEdgeCost_eq M e, c.flux_cost_eq u j M e, MetricGraph.adjustedResistance,
    c.resistance_eq e, c.mass_eq e]
  by_cases ht : G.IsPassiveTip κ (G.tail e)
  · have hj := h.passive_tail_neumann ht
    have hb := (constant_edge_reflecting_left he (c.conductance_pos e) (c.source_pos e)
      (G.length_pos e) hM hj).2
    have hs : (4 * (G.length e / c.conductance e)) * (c.source e * G.length e) ^ 2 / 8 =
        (c.source e * G.length e) ^ 2 * (G.length e / c.conductance e) / 2 := by ring
    simp only [MetricGraph.reflectionFactor, MetricGraph.peakPosition, ht, true_or, ite_true, hs]
    rw [hb]
    simp only [hj, zero_div, zero_pow (by decide : 2 ≠ 0), sub_zero, true_and]
    exact eq_comm.trans sub_eq_zero.symm
  · by_cases hh : G.IsPassiveTip κ (G.head e)
    · have hj := h.passive_head_neumann hh
      have hz : j e 0 / c.source e = G.length e := by
        apply (div_eq_iff (ne_of_gt (c.source_pos e))).mpr
        have hf := constant_edge_flux he ⟨(G.length_pos e).le, le_rfl⟩
        linarith
      have hd : M - u e 0 - j e 0 ^ 2 / (2 * c.conductance e * c.source e) =
          M - u e (G.length e) := by
        have hd := constant_edge_centered he (ne_of_gt (c.conductance_pos e))
          (ne_of_gt (c.source_pos e)) M ⟨(G.length_pos e).le, le_rfl⟩
        simpa only [hz, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hd.symm
      have hb := (constant_edge_reflecting_right he (c.conductance_pos e) (c.source_pos e)
        (G.length_pos e) hM hj).2
      have hs : (4 * (G.length e / c.conductance e)) * (c.source e * G.length e) ^ 2 / 8 =
          (c.source e * G.length e) ^ 2 * (G.length e / c.conductance e) / 2 := by ring
      simp only [MetricGraph.reflectionFactor, MetricGraph.peakPosition, ht, hh, false_or,
        ite_true, ite_false, hs, hz, hd, true_and]
      exact hb.trans (eq_comm.trans sub_eq_zero.symm)
    · have hb := (constant_edge_ordinary_barrier he (c.conductance_pos e) (c.source_pos e)
        (G.length_pos e) hM).2
      simp only [MetricGraph.reflectionFactor, MetricGraph.peakPosition, ht, hh, false_or,
        ite_false, one_mul]
      rw [mul_comm (G.length e / c.conductance e), hb]
      exact and_comm

theorem GraphEquation.sharp_edge_profiles [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j)
    (c : EdgeConstants G) (M : ℝ) (e : E)
    (hM : ∀ x ∈ Icc 0 (G.length e), u e x ≤ M)
    (heq : G.weakEdgeCost u M e = G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8) :
    EqOn (u e) (c.sharpProfile κ M e) (Icc 0 (G.length e)) ∧
      EqOn (j e) (c.sharpFlux κ e) (Icc 0 (G.length e)) := by
  obtain ⟨hz, hd⟩ := (h.sharp_edge_parameters c M e hM).mp heq
  have he := constant_edge_of_eqOn (h.edge_equation e) (c.conductance_eq e) (c.source_eq e)
  constructor
  · intro x hx
    have hf := constant_edge_centered he (ne_of_gt (c.conductance_pos e))
      (ne_of_gt (c.source_pos e)) M hx
    rw [hz, hd, zero_add] at hf
    unfold EdgeConstants.sharpProfile
    have hs : (c.source e / c.conductance e) / 2 = c.source e / (2 * c.conductance e) := by ring
    rw [hs] at hf
    linarith
  · intro x hx
    rw [constant_edge_flux he hx]
    have hj := (div_eq_iff (ne_of_gt (c.source_pos e))).mp hz
    unfold EdgeConstants.sharpFlux
    rw [hj]
    ring

/-- The displayed parabolas solve the original edge equation, without
assuming a graph solution or assuming equality in a bound. -/
theorem EdgeConstants.sharpProfile_equation {G : MetricGraph V E} (c : EdgeConstants G)
    (κ : V → ℝ) (M : ℝ) (e : E) :
    EdgeEquation (G.conductance e) (G.source e) 0 (G.length e)
      (c.sharpProfile κ M e) (c.sharpFlux κ e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (continuous_const.sub (continuous_const.mul
      ((continuous_id.sub continuous_const).pow 2))).continuousOn
  · exact (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
  · intro x hx
    rw [c.conductance_eq e ⟨hx.1.le, hx.2.le⟩]
    unfold EdgeConstants.sharpProfile EdgeConstants.sharpFlux
    convert! ((((hasDerivAt_id x).sub_const (G.peakPosition κ e)).pow 2).const_mul
      (c.source e / (2 * c.conductance e))).const_sub M using 1
    simp only [id_eq]
    ring
  · intro x hx
    rw [c.source_eq e ⟨hx.1.le, hx.2.le⟩]
    unfold EdgeConstants.sharpFlux
    convert! ((hasDerivAt_id x).const_sub (G.peakPosition κ e)).const_mul (c.source e) using 1
    ring

end TimeTraps.Graph
