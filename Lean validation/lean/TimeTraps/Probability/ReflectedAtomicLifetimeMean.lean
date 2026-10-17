module

public import TimeTraps.Probability.ReflectedAtomicLifetimeMeanData

@[expose] public section

/-! The actual extended mean lifetime in the independent exponential
threshold product equals the nonnegative time integral of actual mean
survival. Both sides may be infinite. Only the proved almost-sure clock
regularity is used, without an everywhere regular version. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicClock_measurable (L D x : ℝ) (a κ : ι → ℝ) (r : ℝ) :
    Measurable (reflectedAtomicClock L D x a κ r) := by
  have hm : Measurable (fun ω : ℕ → ℝ => (r, ω)) := measurable_const.prodMk measurable_id
  have h := (reflectedAtomicClock_jointlyMeasurable L D x a κ).comp hm
  have he : reflectedAtomicClock L D x a κ r =
      (Function.uncurry (reflectedAtomicClock L D x a κ) ∘ fun ω : ℕ → ℝ => (r, ω)) := rfl
  rw [he]
  exact h

theorem reflectedAtomicLifetimeValue_aemeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    AEMeasurable (reflectedAtomicLifetimeValue L D x a κ)
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  exact contactLifetimeValue_aemeasurable_of_ae_paths brownianDyadicMeasure
    (reflectedAtomicClock L D x a κ) (fun r _ => reflectedAtomicClock_measurable L D x a κ r)
    (reflectedAtomicClock_paths_ae L hL D hD x a κ hκ)

theorem reflectedAtomicLifetimeValue_mean_survival (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, reflectedAtomicLifetimeValue L D x a κ p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (reflectedAtomicMeanSurvival L D x a κ r.toNNReal) := by
  have hAt : ∀ r : ℝ, 0 ≤ r → Measurable (reflectedAtomicClock L D x a κ r) := by
    intro r _
    exact reflectedAtomicClock_measurable L D x a κ r
  have he := contactLifetime_mean_survival_of_ae_paths brownianDyadicMeasure
    (reflectedAtomicClock L D x a κ) hAt
    (fun r _ ω => reflectedAtomicClock_nonneg L hD x a κ hκ r ω)
    (reflectedAtomicClock_paths_ae L hL D hD x a κ hκ)
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ ω,
        ENNReal.ofReal (Real.exp (-reflectedAtomicClock L D x a κ r ω)) ∂brownianDyadicMeasure := he
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r _
      exact reflectedAtomicSurvival_lintegral L hD x a κ hκ r.toNNReal

theorem reflectedAtomicLifetimeValue_mean_identity (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, reflectedAtomicLifetimeValue L D x a κ p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (reflectedAtomicSurvival L D x a κ r.toNNReal ω)) ∂brownianDyadicMeasure := by
  exact contactLifetime_mean_identity_of_ae_paths brownianDyadicMeasure
    (reflectedAtomicClock L D x a κ) (reflectedAtomicClock_jointlyMeasurable L D x a κ)
    (fun r _ ω => reflectedAtomicClock_nonneg L hD x a κ hκ r ω)
    (reflectedAtomicClock_paths_ae L hL D hD x a κ hκ)

end TimeTraps.Probability
