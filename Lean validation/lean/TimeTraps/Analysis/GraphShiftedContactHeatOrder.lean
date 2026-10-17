module

public import TimeTraps.Analysis.GraphShiftedContactHeatOrderEuler
public import TimeTraps.Analysis.GraphShiftedContactHeatConservative

@[expose] public section

/-! Removing the auxiliary mass shift preserves the derived positivity.
For a graph with zero reactions, the original heat evolution therefore
preserves the interval [0,1] and its pairing with the actual constant one. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_nonneg_ae
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      0 ≤ (P.heatSemigroup t f e) x := by
  intro e
  change ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
    0 ≤ ((Real.exp (t : ℝ) • P.shiftedHeatSemigroup t f) e) x
  simp only [PiLp.smul_apply]
  filter_upwards [P.shiftedHeatSemigroup_nonneg_ae t f hf e,
    Lp.coeFn_smul (Real.exp (t : ℝ)) (P.shiftedHeatSemigroup t f e)] with x hx he
  rw [he]
  exact mul_nonneg (Real.exp_pos _).le hx

theorem GraphShiftedContactOperatorProblem.heatSemigroup_mono_ae
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ (g e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      (P.heatSemigroup t f e) x ≤ (P.heatSemigroup t g e) x := by
  have hp : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ ((g - f) e) x := by
    intro e
    simp only [PiLp.sub_apply]
    filter_upwards [hfg e, Lp.coeFn_sub (g e) (f e)] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro e
  have hi := P.heatSemigroup_nonneg_ae t (g - f) hp e
  rw [map_sub] at hi
  simp only [PiLp.sub_apply] at hi
  filter_upwards [hi, Lp.coeFn_sub (P.heatSemigroup t g e) (P.heatSemigroup t f e)] with x hx he
  apply sub_nonneg.mp
  simpa only [he, Pi.sub_apply] using hx

theorem GraphShiftedContactOperatorProblem.heatSemigroup_unit_interval_ae_of_zero
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x ∧ (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      0 ≤ (P.heatSemigroup t f e) x ∧ (P.heatSemigroup t f e) x ≤ 1 := by
  have hp := P.heatSemigroup_nonneg_ae t f (fun e => (hf e).mono (fun _ hx => hx.1))
  have hb := P.heatSemigroup_mono_ae t f (graphSobolevSpaceStateL P.geometry P.operatorOne) (by
    intro e
    filter_upwards [hf e, P.operatorOne_state_ae e] with x hx he
    rw [he]
    exact hx.2)
  rw [P.heatSemigroup_one hκ] at hb
  intro e
  filter_upwards [hp e, hb e, P.operatorOne_state_ae e] with x hx hy he
  exact ⟨hx, he ▸ hy⟩

theorem GraphShiftedContactOperatorProblem.heatSemigroup_constant_pairing_of_zero
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (f : GraphL2Product P.geometry) :
    inner ℝ (P.heatSemigroup t f) (graphSobolevSpaceStateL P.geometry P.operatorOne) =
      inner ℝ f (graphSobolevSpaceStateL P.geometry P.operatorOne) := by
  have hs : inner ℝ (P.heatSemigroup t f) (graphSobolevSpaceStateL P.geometry P.operatorOne) =
      inner ℝ f (P.heatSemigroup t (graphSobolevSpaceStateL P.geometry P.operatorOne)) :=
    P.heatSemigroup_symmetric t f _
  simpa only [P.heatSemigroup_one hκ] using hs

end TimeTraps.Analysis
