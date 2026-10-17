module

public import TimeTraps.Probability.GraphPointLocalTimeNormalization

@[expose] public section

/-! The literal finite sum of raw-adapted graph point local times is the
atomic killing clock. Empty contact families and zero strengths are
allowed; continuity and monotonicity use one event for all times. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal Topology

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

omit [Fintype I] in
theorem GraphShiftedContactOperatorProblem.pointLocalTime_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : 0 ≤ P.pointLocalTime a t p := by
  let F := fun n p => P.localTimeApproximant a n p t
  change 0 ≤ graphLocalTimeScalarLimit F p
  by_cases h : ∃ l : ℝ, Tendsto (fun n => F n p) atTop (𝓝 l)
  · obtain ⟨l, hl⟩ := h
    rw [graphLocalTimeScalarLimit_eq_of_tendsto F hl]
    exact ge_of_tendsto hl (Eventually.of_forall (fun n => P.localTimeApproximant_nonneg a n p t))
  · rw [graphLocalTimeScalarLimit_zero_off F h]

omit [Fintype I] in
theorem GraphShiftedContactOperatorProblem.pointLocalTime_zero
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) : P.pointLocalTime a 0 p = 0 := by
  change graphLocalTimeScalarLimit (fun n p => P.localTimeApproximant a n p 0) p = 0
  apply graphLocalTimeScalarLimit_eq_of_tendsto
  simpa only [P.localTimeApproximant_zero] using (tendsto_const_nhds (x := (0 : ℝ)))

noncomputable def GraphShiftedContactOperatorProblem.atomicKillingClock
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (t : ℝ) (p : GraphContinuousPath P.geometry) : ℝ :=
  ∑ i, κ i * P.pointLocalTime (a i) t.toNNReal p

theorem GraphShiftedContactOperatorProblem.atomicKillingClock_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry) (κ : I → ℝ) :
    Measurable (Function.uncurry (P.atomicKillingClock a κ)) := by
  let F : I → (ℝ × GraphContinuousPath P.geometry) → ℝ :=
    fun i q => κ i * P.pointLocalTime (a i) q.1.toNNReal q.2
  have hm : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => (q.1.toNNReal, q.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hF : ∀ i, Measurable (F i) := by
    intro i
    have h := (P.pointLocalTime_jointlyMeasurable (a i)).comp hm
    have hmul := h.const_mul (κ i)
    exact hmul
  have hs : Measurable (fun q => ∑ i, F i q) :=
    Finset.measurable_sum _ (fun i _ => hF i)
  have he : Function.uncurry (P.atomicKillingClock a κ) = (fun q => ∑ i, F i q) := rfl
  rw [he]
  exact hs

theorem GraphShiftedContactOperatorProblem.atomicKillingClock_measurable
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (t : ℝ) : Measurable (P.atomicKillingClock a κ t) := by
  have hm : Measurable (fun p : GraphContinuousPath P.geometry => (t, p)) :=
    measurable_const.prodMk measurable_id
  have he : P.atomicKillingClock a κ t =
      (Function.uncurry (P.atomicKillingClock a κ) ∘ fun p => (t, p)) := rfl
  rw [he]
  exact (P.atomicKillingClock_jointlyMeasurable a κ).comp hm

theorem GraphShiftedContactOperatorProblem.atomicKillingClock_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (p : GraphContinuousPath P.geometry) :
    0 ≤ P.atomicKillingClock a κ t p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hκ i) (P.pointLocalTime_nonneg (a i) t.toNNReal p))

theorem GraphShiftedContactOperatorProblem.atomicKillingClock_zero
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (p : GraphContinuousPath P.geometry) : P.atomicKillingClock a κ 0 p = 0 := by
  simp only [GraphShiftedContactOperatorProblem.atomicKillingClock, Real.toNNReal_zero,
    P.pointLocalTime_zero, mul_zero, Finset.sum_const_zero]

theorem GraphShiftedContactOperatorProblem.atomicKillingClock_paths_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, ContinuousOn (fun t => P.atomicKillingClock a κ t p) (Ici 0) ∧
      MonotoneOn (fun t => P.atomicKillingClock a κ t p) (Ici 0) := by
  filter_upwards [ae_all_iff.mpr (fun i => P.pointLocalTime_regular_ae h0 x (a i))] with p hp
  constructor
  · apply Continuous.continuousOn
    apply continuous_finsetSum
    intro i _
    exact ((hp i).1.comp continuous_real_toNNReal).const_mul (κ i)
  · intro s _ t _ hst
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      ((hp i).2.1 (Real.toNNReal_monotone hst)) (hκ i))

end TimeTraps.Analysis
