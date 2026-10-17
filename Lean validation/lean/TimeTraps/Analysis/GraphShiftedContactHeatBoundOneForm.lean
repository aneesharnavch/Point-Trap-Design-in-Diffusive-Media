module

public import TimeTraps.Analysis.GraphShiftedContactHeatBoundOneData

@[expose] public section

/-! The corrected step is bounded by one because its original contact
form has nonnegative reactions. The full H1 absolute-value test proves
the bound without assuming an operator-domain condition on one. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.correctedHeatStep_upper_test_nonpos
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) (hs : 0 < s)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    let w := P.operatorOne - P.correctedHeatStepState s hs f
    P.shiftedHeatResolventPairing s w (w - P.operatorOrderAbs w) ≤ 0 := by
  let u := P.correctedHeatStepState s hs f
  let w := P.operatorOne - u
  let z := w - P.operatorOrderAbs w
  change P.shiftedHeatResolventPairing s w z ≤ 0
  have he := P.correctedHeatStepState_spec s hs f z
  change P.shiftedHeatResolventPairing s u z =
    (1 + (s : ℝ)) * inner ℝ f (graphSobolevSpaceStateL P.geometry z) at he
  have hpair : P.shiftedHeatResolventPairing s w z =
      (1 + (s : ℝ)) * inner ℝ (graphSobolevSpaceStateL P.geometry P.operatorOne - f)
        (graphSobolevSpaceStateL P.geometry z) + (s : ℝ) * P.contactForm P.operatorOne z := by
    change inner ℝ (graphSobolevSpaceStateL P.geometry (P.operatorOne - u))
        (graphSobolevSpaceStateL P.geometry z) + (s : ℝ) * P.operatorForm (P.operatorOne - u) z = _
    simp only [map_sub, inner_sub_left, sub_apply]
    rw [P.operatorForm_eq P.operatorOne z]
    unfold shiftedHeatResolventPairing at he
    nlinarith
  rw [hpair]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (P.operatorOrderAbs_load_nonpos _ (P.operatorOne_sub_source_nonneg f hf) w))
    (mul_nonpos_of_nonneg_of_nonpos s.property (P.contactForm_one_abs_difference_nonpos w))

theorem GraphShiftedContactOperatorProblem.correctedHeatStepState_one_sub_eq_orderAbs
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) (hs : 0 < s)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    P.operatorOne - P.correctedHeatStepState s hs f =
      P.operatorOrderAbs (P.operatorOne - P.correctedHeatStepState s hs f) := by
  let w := P.operatorOne - P.correctedHeatStepState s hs f
  let z := w - P.operatorOrderAbs w
  have hz : P.shiftedHeatResolventPairing s z z ≤ 0 := by
    change P.shiftedHeatResolventPairing s (w - P.operatorOrderAbs w) (w - P.operatorOrderAbs w) ≤ 0
    rw [P.shiftedHeatResolventPairing_abs_difference]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (P.correctedHeatStep_upper_test_nonpos s hs f hf)
  have hp : 0 ≤ (s : ℝ) * P.operatorForm z z :=
    mul_nonneg s.property (P.operatorForm_nonneg z)
  have hm : ‖graphSobolevSpaceStateL P.geometry z‖ ^ 2 ≤ 0 := by
    unfold shiftedHeatResolventPairing at hz
    rw [real_inner_self_eq_norm_sq] at hz
    linarith
  have hstate : graphSobolevSpaceStateL P.geometry z = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (graphSobolevSpaceStateL P.geometry z)]
  have hzero : z = 0 := (graphSobolevSpaceStateL_injective P.geometry)
    (by simpa only [map_zero] using hstate)
  exact sub_eq_zero.mp hzero

end TimeTraps.Analysis
