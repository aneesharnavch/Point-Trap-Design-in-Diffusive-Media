module

public import TimeTraps.Analysis.GraphShiftedContactHeatBoundOneStep
public import TimeTraps.Analysis.GraphShiftedContactHeatOrder

@[expose] public section

/-! Actual corrected graph resolvent powers preserve the upper bound one, and
their strong Euler limit gives the same bound for the original heat flow.
Together with positivity this preserves the edgewise interval [0,1].
These are deterministic operator statements, with no stochastic kernel. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.correctedHeatStep_pow_apply
    (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) (n : ℕ) (f : GraphL2Product P.geometry) :
    ((P.correctedHeatStep s) ^ n) f =
      (1 + (s : ℝ)) ^ n • ((P.shiftedHeatResolvent s) ^ n) f := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self, one_smul]
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih]
      simp only [correctedHeatStep, smul_apply, map_smul, smul_smul, pow_succ', mul_apply_eq_comp, mul_comm]

theorem GraphShiftedContactOperatorProblem.correctedHeatStep_euler_tendsto
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (f : GraphL2Product P.geometry) :
    Tendsto (fun n : ℕ => ((P.correctedHeatStep (t / (n : ℝ≥0))) ^ n) f)
      atTop (𝓝 (P.heatSemigroup t f)) := by
  have hs := (Real.tendsto_one_add_div_pow_exp (t : ℝ)).smul
    (P.shiftedHeatResolvent_euler_tendsto t f)
  change Tendsto _ atTop (𝓝 (Real.exp (t : ℝ) • P.shiftedHeatSemigroup t f))
  convert! hs using 1
  funext n
  rw [P.correctedHeatStep_pow_apply]
  simp only [NNReal.coe_div, NNReal.coe_natCast]

theorem GraphShiftedContactOperatorProblem.correctedHeatStep_pow_le_one_ae (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (n : ℕ) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (((P.correctedHeatStep s) ^ n) f e) x ≤ 1 := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hf
  | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        P.correctedHeatStep_le_one_ae s (((P.correctedHeatStep s) ^ n) f) ih

theorem GraphShiftedContactOperatorProblem.heatSemigroup_le_one_ae (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (P.heatSemigroup t f e) x ≤ 1 := by
  intro e
  let c : Lp ℝ 2 (volume.restrict (Ioo 0 (P.geometry.length e))) :=
    graphSobolevSpaceStateL P.geometry P.operatorOne e
  let y : Lp ℝ 2 (volume.restrict (Ioo 0 (P.geometry.length e))) := P.heatSemigroup t f e
  let U : ℕ → Lp ℝ 2 (volume.restrict (Ioo 0 (P.geometry.length e))) :=
    fun n => ((P.correctedHeatStep (t / (n : ℝ≥0))) ^ n) f e
  have hlim : Tendsto (fun n => c - U n) atTop (𝓝 (c - y)) :=
    tendsto_const_nhds.sub (((graphL2ComponentL P.geometry e).continuous.tendsto _).comp
      (P.correctedHeatStep_euler_tendsto t f))
  have hn (n : ℕ) : ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (c - U n) x := by
    filter_upwards [P.operatorOne_state_ae e,
      P.correctedHeatStep_pow_le_one_ae (t / (n : ℝ≥0)) n f hf e,
      Lp.coeFn_sub c (U n)] with x h₁ hx he
    rw [he, Pi.sub_apply]
    change 0 ≤ (graphSobolevSpaceStateL P.geometry P.operatorOne e) x - (U n) x
    rw [h₁]
    exact sub_nonneg.mpr hx
  have h := ae_nonnegative_of_L2_tendsto (fun n => c - U n)
    (c - y) hlim hn
  filter_upwards [h, P.operatorOne_state_ae e,
    Lp.coeFn_sub c y] with x hx h₁ he
  rw [he, Pi.sub_apply] at hx
  change 0 ≤ (graphSobolevSpaceStateL P.geometry P.operatorOne e) x - (P.heatSemigroup t f e) x at hx
  rw [h₁] at hx
  exact sub_nonneg.mp hx

theorem GraphShiftedContactOperatorProblem.heatSemigroup_unit_interval_ae (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x ∧ (f e) x ≤ 1) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      0 ≤ (P.heatSemigroup t f e) x ∧ (P.heatSemigroup t f e) x ≤ 1 := by
  intro e
  filter_upwards [P.heatSemigroup_nonneg_ae t f (fun d => (hf d).mono fun _ h => h.1) e,
    P.heatSemigroup_le_one_ae t f (fun d => (hf d).mono fun _ h => h.2) e] with x h₀ h₁
  exact ⟨h₀, h₁⟩

end TimeTraps.Analysis
