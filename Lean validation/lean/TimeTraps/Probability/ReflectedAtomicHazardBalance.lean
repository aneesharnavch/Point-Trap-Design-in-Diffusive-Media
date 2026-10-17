module

public import TimeTraps.Probability.ReflectedAtomicSurvivalStieltjes

@[expose] public section

/-! Exact finite-horizon survival balance against the actual hazard
measure. One finite-label event gives every finite horizon. This does
not assume or assert that survival vanishes at infinite time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicHazard_survival_integrable
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (T : ℝ≥0) :
    IntegrableOn (fun r => reflectedAtomicSurvival L D x a κ r.toNNReal ω)
      (Ioc (0 : ℝ) T.val) (reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) := by
  simpa only [one_mul] using
    (reflectedAtomicSurvivalLoss_weighted_integrable L hL D hD x a κ hκ hω
      (fun _ => 1) continuous_const T).2

theorem reflectedAtomicHazard_survival_balance
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
      ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) =
      1 - reflectedAtomicSurvival L D x a κ T ω := by
  let K := reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω
  have hK : Continuous K := reflectedAtomicHazardStieltjes_continuous L hL D hD x a κ hκ ω
  have hf : (fun r : ℝ => Real.exp (-K r)) =
      fun r => reflectedAtomicSurvival L D x a κ r.toNNReal ω := by
    funext r
    change Real.exp (-reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω r) = _
    rw [reflectedAtomicHazardStieltjes_apply L hL D hD x a κ hκ hω r]
    rfl
  have hzero : K 0 = 0 := reflectedAtomicHazardStieltjes_zero L hL D hD x a κ hκ hω
  have hT : K T.val = reflectedAtomicHazard L D x a κ T ω :=
    (reflectedAtomicHazardStieltjes_apply L hL D hD x a κ hκ hω T.val).trans
      (congrArg (fun t => reflectedAtomicHazard L D x a κ t ω) (Real.toNNReal_coe (r := T)))
  have he := stieltjes_exp_neg_integral K hK T
  rw [hf, hzero, neg_zero, Real.exp_zero, hT] at he
  exact he

theorem reflectedAtomicHazard_survival_bound
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (T : ℝ≥0) :
    0 ≤ (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
      ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) ∧
    (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
      ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) ≤ 1 := by
  rw [reflectedAtomicHazard_survival_balance L hL D hD x a κ hκ hω T]
  have hb := reflectedAtomicSurvival_bounds L hD x a κ hκ T ω
  exact ⟨sub_nonneg.mpr hb.2, sub_le_self _ hb.1.le⟩

theorem reflectedAtomicHazard_survival_balance_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      IntegrableOn (fun r => reflectedAtomicSurvival L D x a κ r.toNNReal ω)
        (Ioc (0 : ℝ) T.val) (reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) ∧
      (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
        ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) =
        1 - reflectedAtomicSurvival L D x a κ T ω ∧
      0 ≤ (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
        ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) ∧
      (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
        ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) ≤ 1 := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [hall] with ω hω T
  exact ⟨reflectedAtomicHazard_survival_integrable L hL D hD x a κ hκ hω T,
    reflectedAtomicHazard_survival_balance L hL D hD x a κ hκ hω T,
    reflectedAtomicHazard_survival_bound L hL D hD x a κ hκ hω T⟩

end TimeTraps.Probability
