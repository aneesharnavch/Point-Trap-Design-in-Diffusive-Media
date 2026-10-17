module

public import TimeTraps.Analysis.GraphShiftedContactHeatOrder

@[expose] public section

/-! A positive corrected resolvent step removes the artificial mass
decay. The original constant-one test retains every nonnegative vertex
reaction, so its supersolution property does not require an anchor. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Nonempty E]

omit [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.operatorOne_representative
    (P : GraphShiftedContactOperatorProblem V E) (e : E) :
    EqOn (P.operatorRep P.operatorOne e) (fun _ => 1) (Icc 0 (P.geometry.length e)) :=
  P.operatorRep_ofEnergy (graphShiftedEnergy_one P.geometry) e

variable [Fintype V] [Fintype E]

omit [Nonempty E] [Fintype V] [Fintype E] in
theorem GraphShiftedContactOperatorProblem.operatorOne_sub_source_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      0 ≤ ((graphSobolevSpaceStateL P.geometry P.operatorOne - f) e) x := by
  intro e
  simp only [PiLp.sub_apply]
  filter_upwards [hf e, P.operatorOne_state_ae e,
    Lp.coeFn_sub (graphSobolevSpaceStateL P.geometry P.operatorOne e) (f e)] with x hfx hone hsub
  rw [hsub, Pi.sub_apply, hone]
  exact sub_nonneg.mpr hfx

theorem GraphShiftedContactOperatorProblem.contactForm_one_abs_difference_nonpos
    (P : GraphShiftedContactOperatorProblem V E) (w : GraphSobolevSpace P.geometry) :
    P.contactForm P.operatorOne (w - P.operatorOrderAbs w) ≤ 0 := by
  rw [P.contactForm_one]
  apply Finset.sum_nonpos
  intro v _
  change P.strength v * graphSobolevNodeValueL P.geometry v (w - P.operatorOrderAbs w) ≤ 0
  rw [map_sub]
  change P.strength v * (P.operatorNodes w v - P.operatorNodes (P.operatorOrderAbs w) v) ≤ 0
  rw [P.operatorOrderAbs_nodes]
  exact mul_nonpos_of_nonneg_of_nonpos (P.strength_nonneg v) (sub_nonpos.mpr (le_abs_self _))

noncomputable def GraphShiftedContactOperatorProblem.correctedHeatStep
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  (1 + (s : ℝ)) • P.shiftedHeatResolvent s

theorem GraphShiftedContactOperatorProblem.correctedHeatStep_zero
    (P : GraphShiftedContactOperatorProblem V E) :
    P.correctedHeatStep 0 = ContinuousLinearMap.id ℝ (GraphL2Product P.geometry) := by
  simp only [correctedHeatStep, NNReal.coe_zero, add_zero, one_smul, P.shiftedHeatResolvent_zero]

noncomputable def GraphShiftedContactOperatorProblem.correctedHeatStepState
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) (hs : 0 < s)
    (f : GraphL2Product P.geometry) : GraphSobolevSpace P.geometry :=
  (1 + (s : ℝ)) • P.shiftedHeatResolventState s hs f

theorem GraphShiftedContactOperatorProblem.correctedHeatStepState_state
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) (hs : 0 < s)
    (f : GraphL2Product P.geometry) :
    graphSobolevSpaceStateL P.geometry (P.correctedHeatStepState s hs f) = P.correctedHeatStep s f := by
  simp only [correctedHeatStepState, map_smul, P.shiftedHeatResolventState_state,
    correctedHeatStep, smul_apply]

theorem GraphShiftedContactOperatorProblem.correctedHeatStepState_spec
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) (hs : 0 < s)
    (f : GraphL2Product P.geometry) (v : GraphSobolevSpace P.geometry) :
    P.shiftedHeatResolventPairing s (P.correctedHeatStepState s hs f) v =
      (1 + (s : ℝ)) * inner ℝ f (graphSobolevSpaceStateL P.geometry v) := by
  have he := P.shiftedHeatResolventState_spec s hs f v
  unfold shiftedHeatResolventPairing at he ⊢
  simp only [correctedHeatStepState, map_smul, real_inner_smul_left, smul_apply, smul_eq_mul]
  nlinarith only [congrArg (fun z : ℝ => (1 + (s : ℝ)) * z) he]

end TimeTraps.Analysis
