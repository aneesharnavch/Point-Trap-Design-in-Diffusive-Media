module

public import TimeTraps.Probability.GraphAtomicKillingClock
public import TimeTraps.Probability.GraphPointLocalTimeCocycle

@[expose] public section

/-! Survival is the literal exponential of the graph local-time clock.
It is raw adapted and bounded, with continuous nonincreasing paths and
the multiplicative path-shift identity on one full-measure event. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.atomicKillingClock_coe
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    P.atomicKillingClock a κ (t : ℝ) p = ∑ i, κ i * P.pointLocalTime (a i) t p := by
  simp only [GraphShiftedContactOperatorProblem.atomicKillingClock, Real.toNNReal_coe]

noncomputable def GraphShiftedContactOperatorProblem.atomicSurvival
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  Real.exp (-P.atomicKillingClock a κ (t : ℝ) p)

theorem GraphShiftedContactOperatorProblem.atomicSurvival_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.atomicSurvival a κ) := by
  intro t
  have hm : StronglyMeasurable[graphContinuousNaturalFiltration P.geometry t]
      (fun p => ∑ i, κ i * P.pointLocalTime (a i) t p) := by
    have hs := Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
      ((P.pointLocalTime_stronglyAdapted (a i)) t).const_mul (κ i))
    have he : (∑ i, fun p => κ i * P.pointLocalTime (a i) t p) =
        (fun p => ∑ i, κ i * P.pointLocalTime (a i) t p) := by
      funext p
      exact Finset.sum_apply _ _ _
    rw [he] at hs
    exact hs
  have he : P.atomicSurvival a κ t = (fun p => Real.exp (-(∑ i, κ i * P.pointLocalTime (a i) t p))) := by
    funext p
    simp only [GraphShiftedContactOperatorProblem.atomicSurvival, P.atomicKillingClock_coe]
  rw [he]
  simpa only [Pi.neg_apply] using
    Real.continuous_exp.comp_stronglyMeasurable hm.neg

theorem GraphShiftedContactOperatorProblem.atomicSurvival_bounds
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    0 < P.atomicSurvival a κ t p ∧ P.atomicSurvival a κ t p ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (P.atomicKillingClock_nonneg a κ hκ (t : ℝ) p))⟩

theorem GraphShiftedContactOperatorProblem.atomicSurvival_zero
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (p : GraphContinuousPath P.geometry) : P.atomicSurvival a κ 0 p = 1 := by
  simp only [GraphShiftedContactOperatorProblem.atomicSurvival, NNReal.coe_zero,
    P.atomicKillingClock_zero, neg_zero, Real.exp_zero]

theorem GraphShiftedContactOperatorProblem.atomicSurvival_continuous_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, Continuous (fun t => P.atomicSurvival a κ t p) := by
  filter_upwards [ae_all_iff.mpr (fun i => P.pointLocalTime_regular_ae h0 x (a i))] with p hp
  have hc : Continuous (fun t => ∑ i, κ i * P.pointLocalTime (a i) t p) :=
    continuous_finsetSum _ (fun i _ => ((hp i).1).const_mul (κ i))
  simpa only [GraphShiftedContactOperatorProblem.atomicSurvival, P.atomicKillingClock_coe,
    Function.comp_def, Pi.neg_apply] using
    Real.continuous_exp.comp hc.neg

theorem GraphShiftedContactOperatorProblem.atomicSurvival_cocycle_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, ∀ s t : ℝ≥0,
      P.atomicSurvival a κ (s + t) p = P.atomicSurvival a κ s p *
        P.atomicSurvival a κ t (graphContinuousPathShift P.geometry s p) := by
  filter_upwards [ae_all_iff.mpr (fun i => P.pointLocalTime_cocycle_ae h0 x (a i))] with p hp
  intro s t
  simp only [GraphShiftedContactOperatorProblem.atomicSurvival, P.atomicKillingClock_coe,
    hp, mul_add, Finset.sum_add_distrib, neg_add, Real.exp_add]

end TimeTraps.Analysis
