module

public import TimeTraps.Graph.SharpBounds
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.EssSup

@[expose] public section

/-!
The physical maximum is defined independently as the supremum of all edge
values, proved attained by compactness, and identified with the essential
supremum norm of the positive weak state. No maximizing point is assumed.
-/

namespace TimeTraps.Graph

open Set MeasureTheory Filter
open scoped BigOperators

variable {V E : Type*}

def MetricGraph.stateValues (G : MetricGraph V E) (u : E → ℝ → ℝ) : Set ℝ :=
  ⋃ e, (u e) '' Icc 0 (G.length e)

noncomputable def MetricGraph.stateMaximum (G : MetricGraph V E) (u : E → ℝ → ℝ) : ℝ :=
  sSup (G.stateValues u)

/-- For a finite metric graph the L-infinity norm is the maximum of the
edge essential suprema; vertices have zero edge-length measure. -/
noncomputable def MetricGraph.essentialNorm (G : MetricGraph V E) (u : E → ℝ → ℝ) : ℝ :=
  ⨆ e, essSup (fun x => |u e x|) (volume.restrict (Icc 0 (G.length e)))

theorem GraphEnergy.values_compact [Fintype E] {G : MetricGraph V E} {U : V → ℝ}
    {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) : IsCompact (G.stateValues u) := by
  apply isCompact_iUnion
  intro e
  apply isCompact_Icc.image_of_continuousOn
  simpa only [uIcc_of_le (G.length_pos e).le] using (hu.edge_energy e).continuousOn

theorem MetricGraph.values_nonempty [Nonempty E] (G : MetricGraph V E) (u : E → ℝ → ℝ) :
    (G.stateValues u).Nonempty := by
  let e : E := Classical.choice inferInstance
  exact ⟨u e 0, mem_iUnion.mpr ⟨e, ⟨0, ⟨le_rfl, (G.length_pos e).le⟩, rfl⟩⟩⟩

theorem GraphEnergy.maximum_isGreatest [Fintype E] [Nonempty E] {G : MetricGraph V E}
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) :
    IsGreatest (G.stateValues u) (G.stateMaximum u) :=
  hu.values_compact.isGreatest_sSup (G.values_nonempty u)

theorem GraphEnergy.le_maximum [Fintype E] [Nonempty E] {G : MetricGraph V E}
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u)
    (e : E) {x : ℝ} (hx : x ∈ Icc 0 (G.length e)) : u e x ≤ G.stateMaximum u :=
  hu.maximum_isGreatest.2 (mem_iUnion.mpr ⟨e, ⟨x, hx, rfl⟩⟩)

theorem GraphEnergy.maximum_attained [Fintype E] [Nonempty E] {G : MetricGraph V E}
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) :
    ∃ e x, x ∈ Icc 0 (G.length e) ∧ u e x = G.stateMaximum u := by
  obtain ⟨e, x, hx, heq⟩ := mem_iUnion.mp hu.maximum_isGreatest.1
  exact ⟨e, x, hx, heq⟩

theorem GraphEnergy.maximum_le_iff [Fintype E] [Nonempty E] {G : MetricGraph V E}
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) {M : ℝ} :
    G.stateMaximum u ≤ M ↔ ∀ e x, x ∈ Icc 0 (G.length e) → u e x ≤ M := by
  constructor
  · intro h e x hx
    exact (hu.le_maximum e hx).trans h
  · intro h
    obtain ⟨e, x, hx, heq⟩ := hu.maximum_attained
    rw [← heq]
    exact h e x hx

/-- A continuous function cannot exceed an almost-everywhere upper bound
at an isolated endpoint either, because the edge has positive length. -/
theorem continuous_edge_le_of_ae_le {u : ℝ → ℝ} {L M : ℝ} (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L))
    (hbound : u ≤ᵐ[volume.restrict (Icc 0 L)] fun _ => M) : ∀ x ∈ Icc 0 L, u x ≤ M := by
  have heq : (fun x => min (u x) M) =ᵐ[volume.restrict (Icc 0 L)] u :=
    hbound.mono fun x hx => min_eq_left hx
  have hon := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hL) heq (hu.inf continuousOn_const) hu
  intro x hx
  exact min_eq_left_iff.mp (hon hx)

theorem continuous_edge_essSup_abs_le_iff {u : ℝ → ℝ} {L M : ℝ} (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L)) :
    essSup (fun x => |u x|) (volume.restrict (Icc 0 L)) ≤ M ↔ ∀ x ∈ Icc 0 L, |u x| ≤ M := by
  let : NeZero (volume.restrict (Icc 0 L)) := ⟨by
    intro hz
    have hzv := Measure.restrict_eq_zero.mp hz
    have hp : 0 < volume (Icc 0 L) := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hL)
    exact (ne_of_gt hp) hzv⟩
  obtain ⟨x₀, _, hx₀⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hL.le⟩ hu.abs
  have hb : IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Icc 0 L))) (fun x => |u x|) :=
    ⟨|u x₀|, (ae_restrict_mem measurableSet_Icc).mono fun x hx => hx₀ hx⟩
  have hc : IsCoboundedUnder (· ≤ ·) (ae (volume.restrict (Icc 0 L))) (fun x => |u x|) :=
    isCoboundedUnder_le_of_le _ (fun x => abs_nonneg (u x))
  constructor
  · intro hM
    exact continuous_edge_le_of_ae_le hL hu.abs ((ae_le_essSup hb).mono fun x hx => hx.trans hM)
  · intro hM
    exact essSup_le_of_ae_le M ((ae_restrict_mem measurableSet_Icc).mono fun x hx => hM x hx) hc

theorem GraphEnergy.essentialNorm_le_iff [Fintype E] [Nonempty E] {G : MetricGraph V E}
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) {M : ℝ} :
    G.essentialNorm u ≤ M ↔ ∀ e x, x ∈ Icc 0 (G.length e) → |u e x| ≤ M := by
  have hb : BddAbove (range (fun e => essSup (fun x => |u e x|)
      (volume.restrict (Icc 0 (G.length e))))) := (finite_range _).bddAbove
  rw [MetricGraph.essentialNorm, ciSup_le_iff hb]
  apply forall_congr'
  intro e
  apply continuous_edge_essSup_abs_le_iff (G.length_pos e)
  simpa only [uIcc_of_le (G.length_pos e).le] using (hu.edge_energy e).continuousOn

theorem WeakGraphEquation.maximum_eq_essentialNorm [Fintype V] [Fintype E] [Nonempty E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) : G.stateMaximum u = G.essentialNorm u := by
  apply le_antisymm
  · apply h.energy.maximum_le_iff.mpr
    have hb := h.energy.essentialNorm_le_iff.mp (le_refl (G.essentialNorm u))
    intro e x hx
    exact (le_abs_self (u e x)).trans (hb e x hx)
  · apply h.energy.essentialNorm_le_iff.mpr
    intro e x hx
    rw [abs_of_pos ((h.positive hκ hanchor).2 e x hx)]
    exact h.energy.le_maximum e hx

/-- The displayed mass-resistance inequalities with M equal to the actual
essential-supremum norm of the weak solution. Equality classification is separate. -/
theorem WeakGraphEquation.sharp_mass_resistance_bound [Fintype V] [Fintype E] [Nonempty E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u)
    (c : EdgeConstants G) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    G.totalMass / (∑ v, κ v) +
      (∑ e, G.adjustedResistance κ e * G.edgeMass e ^ 2) / (8 * G.totalMass) ≤ G.essentialNorm u ∧
    G.totalMass / (∑ v, κ v) + G.totalMass / (8 * ∑ e, 1 / G.adjustedResistance κ e) ≤
      G.totalMass / (∑ v, κ v) +
        (∑ e, G.adjustedResistance κ e * G.edgeMass e ^ 2) / (8 * G.totalMass) := by
  rw [← h.maximum_eq_essentialNorm hκ hanchor]
  exact h.mass_resistance_bounds c hκ hanchor (fun e _ hx => h.energy.le_maximum e hx)

end TimeTraps.Graph
