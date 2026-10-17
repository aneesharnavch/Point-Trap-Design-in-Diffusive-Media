module

public import TimeTraps.Probability.GraphAtomicSurvivalPaths
public import TimeTraps.Probability.GraphPointLocalTimeContactIntegral
public import TimeTraps.Probability.ReflectedAtomicHazardStieltjes

@[expose] public section

/-! The canonical hazard measure is the actual finite nonnegative sum
of graph point-local-time measures. Its continuous increasing path equals
the raw adapted clock at every time on one event. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

noncomputable def GraphShiftedContactOperatorProblem.atomicHazardStieltjes
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (_hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) : StieltjesFunction ℝ :=
  ∑ i, Real.toNNReal (κ i) • P.pointLocalTimeStieltjes (a i) p

theorem GraphShiftedContactOperatorProblem.atomicHazardStieltjes_apply
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) (r : ℝ) :
    P.atomicHazardStieltjes a κ hκ p r = ∑ i, κ i * P.pointLocalTimePath (a i) p r.toNNReal := by
  unfold GraphShiftedContactOperatorProblem.atomicHazardStieltjes
  rw [stieltjesFinsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.toNNReal (κ i) : ℝ) * P.pointLocalTimePath (a i) p r.toNNReal = _
  rw [Real.coe_toNNReal _ (hκ i)]

theorem GraphShiftedContactOperatorProblem.atomicHazardStieltjes_continuous
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) :
    Continuous (P.atomicHazardStieltjes a κ hκ p) := by
  have he : (P.atomicHazardStieltjes a κ hκ p : ℝ → ℝ) =
      (fun r => ∑ i, κ i * P.pointLocalTimePath (a i) p r.toNNReal) :=
    funext (P.atomicHazardStieltjes_apply a κ hκ p)
  rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    ((P.pointLocalTimePath (a i) p).continuous.comp continuous_real_toNNReal).const_mul (κ i))

theorem GraphShiftedContactOperatorProblem.atomicHazardStieltjes_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) (r : ℝ) :
    0 ≤ P.atomicHazardStieltjes a κ hκ p r := by
  rw [P.atomicHazardStieltjes_apply]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hκ i) (P.pointLocalTimePath_nonneg (a i) p r.toNNReal))

theorem GraphShiftedContactOperatorProblem.atomicHazardStieltjes_zero
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) :
    P.atomicHazardStieltjes a κ hκ p 0 = 0 := by
  simp only [P.atomicHazardStieltjes_apply, Real.toNNReal_zero, P.pointLocalTimePath_zero,
    mul_zero, Finset.sum_const_zero]

theorem GraphShiftedContactOperatorProblem.atomicHazardStieltjes_eq_clock_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, ∀ r : ℝ,
      P.atomicHazardStieltjes a κ hκ p r = P.atomicKillingClock a κ r p := by
  filter_upwards [ae_all_iff.mpr (fun i => P.pointLocalTime_eq_path_ae h0 x (a i))] with p hp
  intro r
  simp only [P.atomicHazardStieltjes_apply, GraphShiftedContactOperatorProblem.atomicKillingClock, hp]

theorem GraphShiftedContactOperatorProblem.atomicHazardStieltjes_measure_sum
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry) :
    (P.atomicHazardStieltjes a κ hκ p).measure = ∑ i, Real.toNNReal (κ i) • P.pointLocalTimeMeasure (a i) p := by
  classical
  let K : I → StieltjesFunction ℝ := fun i => Real.toNNReal (κ i) • P.pointLocalTimeStieltjes (a i) p
  have hs (s : Finset I) : (∑ i ∈ s, K i).measure = ∑ i ∈ s, (K i).measure := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, StieltjesFunction.measure_zero]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, StieltjesFunction.measure_add, ih, Finset.sum_insert hi]
  change (∑ i, K i).measure = _
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => StieltjesFunction.measure_smul _ _)

end TimeTraps.Analysis
