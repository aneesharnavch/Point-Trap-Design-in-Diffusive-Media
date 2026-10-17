module

public import TimeTraps.Analysis.GraphContactHeatBoundOneForm
public import TimeTraps.Analysis.GraphContactHeatOrderPositive

@[expose] public section

/-! The actual resolvent maps edge data bounded above by one to states
bounded above by one. Positive steps have the same bound on every closed
edge and recovered vertex. The zero step is the actual identity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphContactOperatorProblem.heatResolventState_representative_le_one (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    ∀ e, ∀ x ∈ Icc 0 (P.geometry.length e), P.operatorRep (P.heatResolventState s hs f) e x ≤ 1 := by
  let u := P.heatResolventState s hs f
  let w := P.operatorOne - u
  have hw : w = P.operatorOrderAbs w := P.heatResolventState_one_sub_eq_orderAbs s hs f hf
  intro e x hx
  have ha := P.operatorOrderAbs_representative w e hx
  rw [← hw] at ha
  have hn : 0 ≤ P.operatorRep w e x := ha.symm ▸ abs_nonneg (P.operatorRep w e x)
  have hv : P.operatorRep w e x = 1 - P.operatorRep u e x := by
    change evalL (P.geometry.length_pos e) x hx (P.operatorEdgeL e (P.operatorOne - u)) = _
    rw [map_sub, map_sub]
    change P.operatorRep P.operatorOne e x - P.operatorRep u e x = _
    rw [P.operatorOne_representative e hx]
  rw [hv] at hn
  exact sub_nonneg.mp hn

theorem GraphContactOperatorProblem.heatResolventState_nodes_le_one (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    ∀ v, P.operatorNodes (P.heatResolventState s hs f) v ≤ 1 := by
  let u := P.heatResolventState s hs f
  let w := P.operatorOne - u
  have hw : w = P.operatorOrderAbs w := P.heatResolventState_one_sub_eq_orderAbs s hs f hf
  intro v
  have ha := P.operatorOrderAbs_nodes w v
  rw [← hw] at ha
  have hn : 0 ≤ P.operatorNodes w v := ha.symm ▸ abs_nonneg (P.operatorNodes w v)
  change 0 ≤ graphSobolevNodeValueL P.geometry v (P.operatorOne - u) at hn
  rw [map_sub] at hn
  change 0 ≤ P.operatorNodes P.operatorOne v - P.operatorNodes u v at hn
  rw [P.operatorOne_nodes v] at hn
  exact sub_nonneg.mp hn

theorem GraphContactOperatorProblem.heatResolvent_le_one_ae (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (P.heatResolvent s f e) x ≤ 1 := by
  by_cases hz : s = 0
  · simpa only [hz, P.heatResolvent_zero, ContinuousLinearMap.id_apply] using hf
  · have hs : 0 < s := pos_iff_ne_zero.mpr hz
    intro e
    rw [← P.heatResolventState_state s hs f]
    have hrep : (graphSobolevSpaceStateL P.geometry (P.heatResolventState s hs f)) e
        =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] P.operatorRep (P.heatResolventState s hs f) e :=
      graphSobolevRepresentative_state_ae P.geometry (P.heatResolventState s hs f).val e
    filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with x hx hi
    rw [hx]
    exact P.heatResolventState_representative_le_one s hs f hf e x (Ioo_subset_Icc_self hi)

theorem GraphContactOperatorProblem.heatResolvent_unit_interval_ae (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x ∧ (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      0 ≤ (P.heatResolvent s f e) x ∧ (P.heatResolvent s f e) x ≤ 1 := by
  intro e
  filter_upwards [P.heatResolvent_nonneg_ae s f (fun d => (hf d).mono fun _ h => h.1) e,
    P.heatResolvent_le_one_ae s f (fun d => (hf d).mono fun _ h => h.2) e] with x h₀ h₁
  exact ⟨h₀, h₁⟩

end TimeTraps.Analysis
