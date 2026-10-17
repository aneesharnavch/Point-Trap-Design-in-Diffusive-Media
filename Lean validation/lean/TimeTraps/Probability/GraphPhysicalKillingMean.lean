module

public import TimeTraps.Probability.GraphPhysicalKillingSpeedSlice

@[expose] public section

/-! The literal physical first-attainment mean is the survival-weighted
original-speed integral. Tonelli uses the actual extended lifetime and
allows both sides to be infinite, including empty contact families. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetimeValue_mean_survival
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, P.physicalAtomicAttainmentLifetimeValue b hb a κ p
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ p,
        ENNReal.ofReal (P.atomicSurvival a κ r.toNNReal p *
          P.geometry.physicalSpeed b (p r.toNNReal)) ∂P.continuousPathLaw h0 x := by
  let inst := P.continuousPathLaw_probability h0 x
  let instE := exponentialKilling_probability (P.continuousPathLaw h0 x)
  calc
    _ = ∫⁻ p, (∫⁻ r in Ioi (0 : ℝ), P.physicalAtomicStoppedSpeed b a κ r p)
        ∂exponentialKillingMeasure (P.continuousPathLaw h0 x) :=
      lintegral_congr (P.physicalAtomicAttainmentLifetimeValue_stoppedIntegral b hb a κ)
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ p, P.physicalAtomicStoppedSpeed b a κ r p
        ∂exponentialKillingMeasure (P.continuousPathLaw h0 x) :=
      (lintegral_lintegral_swap
        (P.physicalAtomicStoppedSpeed_jointly_aemeasurable h0 b x a κ hκ)).symm
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact P.physicalAtomicStoppedSpeed_lintegral h0 b x a κ hκ r hr.le

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetimeValue_mean_identity
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, P.physicalAtomicAttainmentLifetimeValue b hb a κ p
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) =
      ∫⁻ p, (∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (P.atomicSurvival a κ r.toNNReal p *
          P.geometry.physicalSpeed b (p r.toNNReal))) ∂P.continuousPathLaw h0 x := by
  let inst := P.continuousPathLaw_probability h0 x
  let instE := exponentialKilling_probability (P.continuousPathLaw h0 x)
  exact (P.physicalAtomicAttainmentLifetimeValue_mean_survival h0 b hb x a κ hκ).trans
    (lintegral_lintegral_swap (P.physicalAtomicSurvivalSpeed_jointlyMeasurable b a κ).aemeasurable)

end TimeTraps.Analysis
