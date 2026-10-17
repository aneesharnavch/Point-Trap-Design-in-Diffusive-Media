module

public import TimeTraps.Probability.GraphPhysicalKillingSpeedData

@[expose] public section

/-! Integrating the independent threshold gives the actual survival
weight times the original Borel speed. This extended integral identity
requires neither a finite lifetime nor a finite expected running cost. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.physicalAtomicStoppedSpeed_lintegral
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (r : ℝ) (hr : 0 ≤ r) :
    (∫⁻ p, P.physicalAtomicStoppedSpeed b a κ r p
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) =
      ∫⁻ p, ENNReal.ofReal (P.atomicSurvival a κ r.toNNReal p *
        P.geometry.physicalSpeed b (p r.toNNReal)) ∂P.continuousPathLaw h0 x := by
  let inst := P.continuousPathLaw_probability h0 x
  let instExp := unitExponential_probability
  let instE := exponentialKilling_probability (P.continuousPathLaw h0 x)
  have hs : MeasurableSet {p : GraphContinuousPath P.geometry × ℝ |
      P.atomicKillingClock a κ r p.1 < p.2} :=
    measurableSet_lt ((P.atomicKillingClock_measurable a κ r).comp measurable_fst) measurable_snd
  have hρ : Measurable (fun p : GraphContinuousPath P.geometry × ℝ =>
      ENNReal.ofReal (P.geometry.physicalSpeed b (p.1 r.toNNReal))) :=
    ((P.geometry.physicalSpeed_measurable b).comp
      ((continuous_eval_const r.toNNReal).measurable.comp measurable_fst)).ennreal_ofReal
  have hm : Measurable (fun p : GraphContinuousPath P.geometry × ℝ =>
      if P.atomicKillingClock a κ r p.1 < p.2
      then ENNReal.ofReal (P.geometry.physicalSpeed b (p.1 r.toNNReal)) else 0) :=
    hρ.indicator hs
  calc
    _ = ∫⁻ p : GraphContinuousPath P.geometry × ℝ,
        (if P.atomicKillingClock a κ r p.1 < p.2
        then ENNReal.ofReal (P.geometry.physicalSpeed b (p.1 r.toNNReal)) else 0)
          ∂(P.continuousPathLaw h0 x).prod (expMeasure 1) :=
      lintegral_congr_ae (P.physicalAtomicStoppedSpeed_threshold_ae h0 b x a κ hκ r hr)
    _ = ∫⁻ p, ∫⁻ z,
        (if P.atomicKillingClock a κ r p < z
        then ENNReal.ofReal (P.geometry.physicalSpeed b (p r.toNNReal)) else 0)
          ∂expMeasure 1 ∂P.continuousPathLaw h0 x := lintegral_prod _ hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro p
      change (∫⁻ z, (Ioi (P.atomicKillingClock a κ r p)).indicator
        (fun _ => ENNReal.ofReal (P.geometry.physicalSpeed b (p r.toNNReal))) z ∂expMeasure 1) = _
      rw [lintegral_indicator_const measurableSet_Ioi,
        unitExponential_tail _ (P.atomicKillingClock_nonneg a κ hκ r p)]
      simp only [GraphShiftedContactOperatorProblem.atomicSurvival, Real.coe_toNNReal r hr]
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem GraphShiftedContactOperatorProblem.physicalAtomicSurvivalSpeed_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) :
    Measurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      ENNReal.ofReal (P.atomicSurvival a κ q.1.toNNReal q.2 *
        P.geometry.physicalSpeed b (q.2 q.1.toNNReal))) := by
  have hp : Measurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      ((q.1.toNNReal : ℝ), q.2)) := by fun_prop
  have hA := (P.atomicKillingClock_jointlyMeasurable a κ).comp hp
  have hX : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => q.2 q.1.toNNReal) := by
    fun_prop
  have hρ := (P.geometry.physicalSpeed_measurable b).comp hX
  have hm := (hA.neg.exp.mul hρ).ennreal_ofReal
  exact hm

end TimeTraps.Analysis
