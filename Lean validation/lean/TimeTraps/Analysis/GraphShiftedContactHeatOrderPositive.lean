module

public import TimeTraps.Analysis.GraphShiftedContactHeatOrderResolvent

@[expose] public section

/-! Order positivity of the actual network resolvent follows from its
derived full H1 equation. Mass and the actual shifted quadratic form are
preserved by absolute value, and mass-shift coercivity identifies the state
with its absolute representative. The zero step is handled by identity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolventState_eq_orderAbs (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    P.shiftedHeatResolventState s hs f = P.operatorOrderAbs (P.shiftedHeatResolventState s hs f) := by
  let u := P.shiftedHeatResolventState s hs f
  let v := P.operatorOrderAbs u
  have hn : P.shiftedHeatResolventPairing s (u - v) (u - v) ≤ 0 := by
    change P.shiftedHeatResolventPairing s (u - P.operatorOrderAbs u) (u - P.operatorOrderAbs u) ≤ 0
    rw [P.shiftedHeatResolventPairing_abs_difference]
    have he : P.shiftedHeatResolventPairing s u (u - P.operatorOrderAbs u) =
        inner ℝ f (graphSobolevSpaceStateL P.geometry (u - P.operatorOrderAbs u)) :=
      P.shiftedHeatResolventState_spec s hs f _
    rw [he]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (P.operatorOrderAbs_load_nonpos f hf u)
  have hb : P.operatorForm (u - v) (u - v) ≤ 0 := by
    have hm : 0 ≤ inner ℝ (graphSobolevSpaceStateL P.geometry (u - v))
        (graphSobolevSpaceStateL P.geometry (u - v)) := real_inner_self_nonneg
    change inner ℝ (graphSobolevSpaceStateL P.geometry (u - v))
      (graphSobolevSpaceStateL P.geometry (u - v)) + (s : ℝ) * P.operatorForm (u - v) (u - v) ≤ 0 at hn
    have hp : (s : ℝ) * P.operatorForm (u - v) (u - v) ≤ 0 := by linarith
    exact le_of_not_gt fun hpos =>
      (not_le_of_gt (mul_pos (show 0 < (s : ℝ) from hs) hpos)) hp
  obtain ⟨c, hc, hbound⟩ := P.operatorForm_coercive
  have hz := (hbound (u - v)).trans hb
  change u = v
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  by_contra hn
  have hp : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hz

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolventState_representative_nonneg (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ x ∈ Icc 0 (P.geometry.length e), 0 ≤ P.operatorRep (P.shiftedHeatResolventState s hs f) e x := by
  intro e x hx
  have he := P.operatorOrderAbs_representative (P.shiftedHeatResolventState s hs f) e hx
  rw [← P.shiftedHeatResolventState_eq_orderAbs s hs f hf] at he
  exact he.symm ▸ abs_nonneg (P.operatorRep (P.shiftedHeatResolventState s hs f) e x)

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolventState_nodes_nonneg (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ v, 0 ≤ P.operatorNodes (P.shiftedHeatResolventState s hs f) v := by
  intro v
  have he := P.operatorOrderAbs_nodes (P.shiftedHeatResolventState s hs f) v
  rw [← P.shiftedHeatResolventState_eq_orderAbs s hs f hf] at he
  exact he.symm ▸ abs_nonneg (P.operatorNodes (P.shiftedHeatResolventState s hs f) v)

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolvent_nonneg_ae (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (P.shiftedHeatResolvent s f e) x := by
  by_cases hz : s = 0
  · simpa only [hz, P.shiftedHeatResolvent_zero, ContinuousLinearMap.id_apply] using hf
  · have hs : 0 < s := pos_iff_ne_zero.mpr hz
    intro e
    rw [← P.shiftedHeatResolventState_state s hs f]
    have hrep : (graphSobolevSpaceStateL P.geometry (P.shiftedHeatResolventState s hs f)) e
        =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] P.operatorRep (P.shiftedHeatResolventState s hs f) e :=
      graphSobolevRepresentative_state_ae P.geometry (P.shiftedHeatResolventState s hs f).val e
    filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with x hx hi
    rw [hx]
    exact P.shiftedHeatResolventState_representative_nonneg s hs f hf e x (Ioo_subset_Icc_self hi)

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolvent_mono_ae (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ (g e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      (P.shiftedHeatResolvent s f e) x ≤ (P.shiftedHeatResolvent s g e) x := by
  have hp : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ ((g - f) e) x := by
    intro e
    simp only [PiLp.sub_apply]
    filter_upwards [hfg e, Lp.coeFn_sub (g e) (f e)] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro e
  have hi := P.shiftedHeatResolvent_nonneg_ae s (g - f) hp e
  rw [map_sub] at hi
  simp only [PiLp.sub_apply] at hi
  filter_upwards [hi, Lp.coeFn_sub (P.shiftedHeatResolvent s g e) (P.shiftedHeatResolvent s f e)] with x hx he
  apply sub_nonneg.mp
  simpa only [he, Pi.sub_apply] using hx

end TimeTraps.Analysis
