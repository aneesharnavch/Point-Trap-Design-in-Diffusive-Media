module

public import TimeTraps.Analysis.GraphContactHeatBoundOneConstant
public import TimeTraps.Analysis.GraphContactHeatOrderResolvent

@[expose] public section

/-! The constant one is a supersolution of the full network resolvent
form. The test w-|w| is an actual vertex-continuous H1 function. Its
vertex reaction terms have the required sign and are not discarded. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem GraphContactOperatorProblem.operatorOne_sub_source_nonneg (P : GraphContactOperatorProblem V E)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      0 ≤ ((graphSobolevSpaceStateL P.geometry P.operatorOne - f) e) x := by
  intro e
  simp only [PiLp.sub_apply]
  filter_upwards [hf e, P.operatorOne_state_ae e,
    Lp.coeFn_sub (graphSobolevSpaceStateL P.geometry P.operatorOne e) (f e)] with x hfx hone hsub
  rw [hsub, Pi.sub_apply, hone]
  exact sub_nonneg.mpr hfx

theorem GraphContactOperatorProblem.operatorForm_one_abs_difference_nonpos (P : GraphContactOperatorProblem V E)
    (w : GraphSobolevSpace P.geometry) :
    P.operatorForm P.operatorOne (w - P.operatorOrderAbs w) ≤ 0 := by
  rw [P.operatorForm_one]
  apply Finset.sum_nonpos
  intro v _
  change P.strength v * graphSobolevNodeValueL P.geometry v (w - P.operatorOrderAbs w) ≤ 0
  rw [map_sub]
  change P.strength v * (P.operatorNodes w v - P.operatorNodes (P.operatorOrderAbs w) v) ≤ 0
  rw [P.operatorOrderAbs_nodes]
  exact mul_nonpos_of_nonneg_of_nonpos (P.strength_nonneg v) (sub_nonpos.mpr (le_abs_self _))

theorem GraphContactOperatorProblem.heatResolvent_upper_test_nonpos (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    let w := P.operatorOne - P.heatResolventState s hs f
    P.heatResolventPairing s w (w - P.operatorOrderAbs w) ≤ 0 := by
  let u := P.heatResolventState s hs f
  let w := P.operatorOne - u
  let z := w - P.operatorOrderAbs w
  change P.heatResolventPairing s w z ≤ 0
  have he := P.heatResolventState_spec s hs f z
  change P.heatResolventPairing s u z = inner ℝ f (graphSobolevSpaceStateL P.geometry z) at he
  have hpair : P.heatResolventPairing s w z =
      inner ℝ (graphSobolevSpaceStateL P.geometry P.operatorOne - f)
        (graphSobolevSpaceStateL P.geometry z) + (s : ℝ) * P.operatorForm P.operatorOne z := by
    change inner ℝ (graphSobolevSpaceStateL P.geometry (P.operatorOne - u))
        (graphSobolevSpaceStateL P.geometry z) + (s : ℝ) * P.operatorForm (P.operatorOne - u) z = _
    simp only [map_sub, inner_sub_left, sub_apply]
    unfold heatResolventPairing at he
    linarith
  rw [hpair]
  exact add_nonpos
    (P.operatorOrderAbs_load_nonpos _ (P.operatorOne_sub_source_nonneg f hf) w)
    (mul_nonpos_of_nonneg_of_nonpos s.property (P.operatorForm_one_abs_difference_nonpos w))

theorem GraphContactOperatorProblem.heatResolventState_one_sub_eq_orderAbs (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    P.operatorOne - P.heatResolventState s hs f =
      P.operatorOrderAbs (P.operatorOne - P.heatResolventState s hs f) := by
  let w := P.operatorOne - P.heatResolventState s hs f
  let z := w - P.operatorOrderAbs w
  have hz : P.heatResolventPairing s z z ≤ 0 := by
    change P.heatResolventPairing s (w - P.operatorOrderAbs w) (w - P.operatorOrderAbs w) ≤ 0
    rw [P.heatResolventPairing_abs_difference]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (P.heatResolvent_upper_test_nonpos s hs f hf)
  have hp : 0 ≤ (s : ℝ) * P.operatorForm z z :=
    mul_nonneg s.property (P.operatorForm_nonneg z)
  have hm : ‖graphSobolevSpaceStateL P.geometry z‖ ^ 2 ≤ 0 := by
    unfold heatResolventPairing at hz
    rw [real_inner_self_eq_norm_sq] at hz
    linarith
  have hstate : graphSobolevSpaceStateL P.geometry z = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (graphSobolevSpaceStateL P.geometry z)]
  have hzero : z = 0 := (graphSobolevSpaceStateL_injective P.geometry)
    (by simpa only [map_zero] using hstate)
  exact sub_eq_zero.mp hzero

end TimeTraps.Analysis
