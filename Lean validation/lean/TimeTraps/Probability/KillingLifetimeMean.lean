module

public import TimeTraps.Probability.KillingLifetimeMeanLayercake

@[expose] public section

/-! The actual extended mean of strict-threshold killing.
Both sides take values in `ℝ≥0∞`, so these identities allow infinite
lifetimes and infinite expected lifetimes. The contact clock is supplied
as measurable path data; no diffusion or local-time construction is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory
open scoped ENNReal

theorem contactLifetime_mean_survival {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable (A t))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t → ∀ ω, 0 ≤ A t ω)
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    (∫⁻ p, contactLifetimeValue A p ∂exponentialKillingMeasure μ) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (Real.exp (-A t ω)) ∂μ := by
  rw [contactLifetime_layercake μ A hA hc hm]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact contactLifetime_survival μ A t ht.le (hA t ht.le) (hAnonneg t ht.le) hc hm

theorem contactLifetime_survival_tonelli {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (Real.exp (-A t ω)) ∂μ) =
      ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-A t ω))) ∂μ := by
  apply lintegral_lintegral_swap
  exact (by fun_prop : Measurable
    (Function.uncurry (fun t ω => ENNReal.ofReal (Real.exp (-A t ω))))).aemeasurable

theorem contactLifetime_mean_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t → ∀ ω, 0 ≤ A t ω)
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    (∫⁻ p, contactLifetimeValue A p ∂exponentialKillingMeasure μ) =
      ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-A t ω))) ∂μ := by
  have hAt : ∀ t : ℝ, 0 ≤ t → Measurable (A t) := by
    intro t _
    exact hA.comp (measurable_const.prodMk measurable_id)
  exact (contactLifetime_mean_survival μ A hAt hAnonneg hc hm).trans
    (contactLifetime_survival_tonelli μ A hA)

end TimeTraps.Probability
