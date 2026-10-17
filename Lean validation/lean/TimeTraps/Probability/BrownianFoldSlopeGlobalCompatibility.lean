module

public import TimeTraps.Probability.BrownianFoldSlopeContinuous

@[expose] public section

/-! Integer-horizon fold integrals agree on a single countably described
measurable event. Dense-time agreement extends to their entire common
interval by continuity; zero starting values are included in the event. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def brownianFoldSlopeGlobalCompatible (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (ω : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, brownianFoldSlopeHorizonPath L hL x hσ n 0 ω = 0) ∧
  ∀ n m k : ℕ,
    brownianFoldSlopeHorizonPath L hL x hσ n (brownianIntegralCommonTime n m k) ω =
      brownianFoldSlopeHorizonPath L hL x hσ m (brownianIntegralCommonTime n m k) ω

theorem brownianFoldSlopeGlobalCompatible_measurableSet (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    MeasurableSet {ω | brownianFoldSlopeGlobalCompatible L hL x hσ ω} := by
  have hz : MeasurableSet {ω | ∀ n : ℕ, brownianFoldSlopeHorizonPath L hL x hσ n 0 ω = 0} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun n => measurableSet_eq_fun
      (brownianFoldSlopeHorizonPath_measurable L hL x hσ n 0) measurable_const)
  have he : MeasurableSet {ω | ∀ n m k : ℕ,
      brownianFoldSlopeHorizonPath L hL x hσ n (brownianIntegralCommonTime n m k) ω =
        brownianFoldSlopeHorizonPath L hL x hσ m (brownianIntegralCommonTime n m k) ω} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun m => MeasurableSet.iInter
      (fun k => measurableSet_eq_fun (brownianFoldSlopeHorizonPath_measurable L hL x hσ n _)
        (brownianFoldSlopeHorizonPath_measurable L hL x hσ m _))))
  exact hz.inter he

theorem brownianFoldSlopeGlobalCompatible_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianFoldSlopeGlobalCompatible L hL x hσ ω := by
  have hz : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      brownianFoldSlopeHorizonPath L hL x hσ n 0 ω = 0 :=
    ae_all_iff.mpr (fun n => brownianFoldSlopeHorizonPath_zero_ae L hL x hσ n)
  have he : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n m k : ℕ,
      brownianFoldSlopeHorizonPath L hL x hσ n (brownianIntegralCommonTime n m k) ω =
        brownianFoldSlopeHorizonPath L hL x hσ m (brownianIntegralCommonTime n m k) ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro k
    have ht := (denseSeq (BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0))) k).property.2
    have hn : brownianIntegralCommonTime n m k ≤ (n : ℝ≥0) := ht.trans (min_le_left _ _)
    have hm : brownianIntegralCommonTime n m k ≤ (m : ℝ≥0) := ht.trans (min_le_right _ _)
    have hen := brownianFoldSlopeHorizonPath_integral_ae L hL x hσ n (brownianIntegralCommonTime n m k)
    have hem := brownianFoldSlopeHorizonPath_integral_ae L hL x hσ m (brownianIntegralCommonTime n m k)
    rw [min_eq_left hn] at hen
    rw [min_eq_left hm] at hem
    exact hen.trans hem.symm
  filter_upwards [hz, he] with ω hzero heq
  exact ⟨hzero, heq⟩

theorem brownianFoldSlopeGlobalCompatible_eq {L x σ : ℝ} {hL : 0 < L} {hσ : 0 < σ}
    {ω : ℕ → ℝ} (hω : brownianFoldSlopeGlobalCompatible L hL x hσ ω)
    (n m : ℕ) (t : ℝ≥0) (hn : t ≤ n) (hm : t ≤ m) :
    brownianFoldSlopeHorizonPath L hL x hσ n t ω = brownianFoldSlopeHorizonPath L hL x hσ m t ω := by
  have he : (fun s : BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0)) =>
      brownianFoldSlopeHorizonPath L hL x hσ n s.val ω) =
      (fun s : BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0)) =>
        brownianFoldSlopeHorizonPath L hL x hσ m s.val ω) := by
    apply (denseRange_denseSeq (BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0)))).equalizer
      ((brownianFoldSlopeHorizonPath_continuous L hL x hσ n ω).comp continuous_subtype_val)
      ((brownianFoldSlopeHorizonPath_continuous L hL x hσ m ω).comp continuous_subtype_val)
    exact funext (hω.2 n m)
  exact congrFun he ⟨t, zero_le, le_min hn hm⟩

end TimeTraps.Probability

end
