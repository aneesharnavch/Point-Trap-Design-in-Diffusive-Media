module

public import TimeTraps.Graph.EqualityProfiles

@[expose] public section

/-!
Incidence accounting for equality: half an ordinary mass at each end, and a
whole pendant mass at its core. The formulas count both ends of a loop.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators Classical

variable {V E : Type*}

noncomputable def MetricGraph.edgeShare (G : MetricGraph V E) (κ : V → ℝ) (e : E) : ℝ := by
  classical
  exact if G.reflectionFactor κ e = 1 then G.edgeMass e / 2 else G.edgeMass e

noncomputable def MetricGraph.coreLoad [Fintype E] (G : MetricGraph V E) (κ : V → ℝ) : V → ℝ :=
  incidenceLoad G.tail G.head (G.edgeShare κ) (G.edgeShare κ)

noncomputable def MetricGraph.sharpLoad [Fintype E] (G : MetricGraph V E) (κ : V → ℝ) (v : V) : ℝ := by
  classical
  exact if G.IsPassiveTip κ v then 0 else G.coreLoad κ v

theorem MetricGraph.edgeShare_pos (G : MetricGraph V E) (κ : V → ℝ) (e : E) :
    0 < G.edgeShare κ e := by
  unfold MetricGraph.edgeShare
  split_ifs
  · exact div_pos (G.edgeMass_pos e) (by positivity)
  · exact G.edgeMass_pos e

theorem MetricGraph.coreLoad_pos [Fintype E] [Nonempty E] (G : MetricGraph V E)
    (κ : V → ℝ) (v : V) : 0 < G.coreLoad κ v :=
  incidenceLoad_pos G.tail G.head _ _ (G.edgeShare_pos κ) (G.edgeShare_pos κ) G.connected v

/-- The exact two sums displayed in the paper; each is an incidence sum. -/
theorem MetricGraph.coreLoad_formula [Fintype E] (G : MetricGraph V E) (κ : V → ℝ) (v : V) :
    G.coreLoad κ v = (1 / 2 : ℝ) * incidenceLoad G.tail G.head
      (fun e => if G.reflectionFactor κ e = 1 then G.edgeMass e else 0)
      (fun e => if G.reflectionFactor κ e = 1 then G.edgeMass e else 0) v +
      incidenceLoad G.tail G.head
      (fun e => if G.reflectionFactor κ e = 4 then G.edgeMass e else 0)
      (fun e => if G.reflectionFactor κ e = 4 then G.edgeMass e else 0) v := by
  classical
  unfold MetricGraph.coreLoad incidenceLoad
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : G.IsPassiveTip κ (G.tail e) ∨ G.IsPassiveTip κ (G.head e)
  all_goals
    simp [MetricGraph.edgeShare, MetricGraph.reflectionFactor, hp] <;> split_ifs <;> ring

theorem MetricGraph.sharpLoad_eq_incidence [Fintype E] (G : MetricGraph V E)
    (κ : V → ℝ) (v : V) :
    G.sharpLoad κ v = incidenceLoad G.tail G.head
      (fun e => if G.IsPassiveTip κ (G.tail e) then 0 else G.edgeShare κ e)
      (fun e => if G.IsPassiveTip κ (G.head e) then 0 else G.edgeShare κ e) v := by
  classical
  unfold MetricGraph.sharpLoad MetricGraph.coreLoad incidenceLoad
  by_cases hp : G.IsPassiveTip κ v
  · rw [if_pos hp]
    symm
    apply Finset.sum_eq_zero
    intro e _
    by_cases ht : G.tail e = v <;> by_cases hh : G.head e = v <;> simp [ht, hh, hp]
  · rw [if_neg hp]
    apply Finset.sum_congr rfl
    intro e _
    by_cases ht : G.tail e = v <;> by_cases hh : G.head e = v <;> simp [ht, hh, hp]

/-- The two exact outgoing fluxes, under the necessary exclusion of an edge
whose two tips are both passive. -/
theorem EdgeConstants.sharpFlux_endpoints {G : MetricGraph V E} (c : EdgeConstants G)
    (κ : V → ℝ) (e : E)
    (hno : ¬(G.IsPassiveTip κ (G.tail e) ∧ G.IsPassiveTip κ (G.head e))) :
    c.sharpFlux κ e 0 = (if G.IsPassiveTip κ (G.tail e) then 0 else G.edgeShare κ e) ∧
    -c.sharpFlux κ e (G.length e) =
      (if G.IsPassiveTip κ (G.head e) then 0 else G.edgeShare κ e) := by
  classical
  by_cases ht : G.IsPassiveTip κ (G.tail e)
  · have hh : ¬G.IsPassiveTip κ (G.head e) := fun hh => hno ⟨ht, hh⟩
    simp [EdgeConstants.sharpFlux, MetricGraph.peakPosition, MetricGraph.edgeShare,
      MetricGraph.reflectionFactor, ht, hh, c.mass_eq]
  · by_cases hh : G.IsPassiveTip κ (G.head e)
    · simp [EdgeConstants.sharpFlux, MetricGraph.peakPosition, MetricGraph.edgeShare,
        MetricGraph.reflectionFactor, ht, hh, c.mass_eq]
    · simp only [EdgeConstants.sharpFlux, MetricGraph.peakPosition, MetricGraph.edgeShare,
        MetricGraph.reflectionFactor, ht, hh, false_or, ite_false, ite_true, c.mass_eq]
      constructor <;> ring

/-- Endpoint deficits of the displayed parabolas. At a passive tip the deficit
is zero; at every core end it is the adjusted mass divided by eight. -/
theorem EdgeConstants.sharpProfile_endpoints {G : MetricGraph V E} (c : EdgeConstants G)
    (κ : V → ℝ) (M : ℝ) (e : E)
    (hno : ¬(G.IsPassiveTip κ (G.tail e) ∧ G.IsPassiveTip κ (G.head e))) :
    c.sharpProfile κ M e 0 =
      (if G.IsPassiveTip κ (G.tail e) then M else M - G.adjustedResistance κ e * G.edgeMass e / 8) ∧
    c.sharpProfile κ M e (G.length e) =
      (if G.IsPassiveTip κ (G.head e) then M else M - G.adjustedResistance κ e * G.edgeMass e / 8) := by
  classical
  by_cases ht : G.IsPassiveTip κ (G.tail e)
  · have hh : ¬G.IsPassiveTip κ (G.head e) := fun hh => hno ⟨ht, hh⟩
    simp only [EdgeConstants.sharpProfile, MetricGraph.peakPosition, MetricGraph.adjustedResistance,
      MetricGraph.reflectionFactor, ht, hh, true_or, ite_true, ite_false, c.resistance_eq, c.mass_eq]
    constructor <;> ring
  · by_cases hh : G.IsPassiveTip κ (G.head e)
    · simp only [EdgeConstants.sharpProfile, MetricGraph.peakPosition, MetricGraph.adjustedResistance,
        MetricGraph.reflectionFactor, ht, hh, false_or, ite_true, ite_false, c.resistance_eq, c.mass_eq]
      constructor <;> ring
    · simp only [EdgeConstants.sharpProfile, MetricGraph.peakPosition, MetricGraph.adjustedResistance,
        MetricGraph.reflectionFactor, ht, hh, false_or, ite_false, c.resistance_eq, c.mass_eq]
      constructor <;> ring

theorem MetricGraph.sharpLoad_sum [Fintype V] [Fintype E] (G : MetricGraph V E)
    (κ : V → ℝ) (hno : ∀ e, ¬(G.IsPassiveTip κ (G.tail e) ∧ G.IsPassiveTip κ (G.head e))) :
    ∑ v, G.sharpLoad κ v = G.totalMass := by
  classical
  simp_rw [G.sharpLoad_eq_incidence κ]
  rw [incidenceLoad_sum]
  change (∑ e, _) = ∑ e, G.edgeMass e
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : G.IsPassiveTip κ (G.tail e)
  · have hh : ¬G.IsPassiveTip κ (G.head e) := fun hh => hno e ⟨ht, hh⟩
    simp [MetricGraph.edgeShare, MetricGraph.reflectionFactor, ht, hh]
  · by_cases hh : G.IsPassiveTip κ (G.head e)
    · simp [MetricGraph.edgeShare, MetricGraph.reflectionFactor, ht, hh]
    · simp [MetricGraph.edgeShare, MetricGraph.reflectionFactor, ht, hh]

theorem GraphEquation.sharp_vertex_balance [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j)
    (c : EdgeConstants G) (M : ℝ)
    (hM : ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M)
    (heq : ∀ e, G.weakEdgeCost u M e = G.adjustedResistance κ e * G.edgeMass e ^ 2 / 8)
    (v : V) : κ v * U v = G.sharpLoad κ v := by
  classical
  rw [h.vertex_balance v, G.sharpLoad_eq_incidence κ v]
  unfold vertexFlux incidenceLoad
  apply Finset.sum_congr rfl
  intro e _
  have hj := (h.sharp_edge_profiles c M e (hM e) (heq e)).2
  have hf := c.sharpFlux_endpoints κ e (h.not_two_passive_tips e)
  dsimp only
  rw [hj ⟨le_rfl, (G.length_pos e).le⟩, hj ⟨(G.length_pos e).le, le_rfl⟩, hf.1, hf.2]

end TimeTraps.Graph
