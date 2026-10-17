module

public import TimeTraps.Probability.KillingLifetimeConventionAE
public import TimeTraps.Probability.ReflectedAtomicLifetimeSurvival

@[expose] public section

/-! The paper's first-attainment lifetime for the actual atomic clock.
It equals the previously constructed strict-exceedance lifetime almost
surely in the independent exponential product. Thus the literal closed
threshold convention has the same survival and extended mean identities.
Plateaus, empty contact families and infinite lifetimes are retained.
No shift-additivity or PCAF assertion is made. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

noncomputable def reflectedAtomicAttainmentLifetime (L D x : ℝ) (a κ : ι → ℝ)
    (p : (ℕ → ℝ) × ℝ) : WithTop ℝ :=
  contactAttainmentLifetime (reflectedAtomicClock L D x a κ) p

noncomputable def reflectedAtomicAttainmentLifetimeValue (L D x : ℝ) (a κ : ι → ℝ)
    (p : (ℕ → ℝ) × ℝ) : ℝ≥0∞ :=
  contactAttainmentLifetimeValue (reflectedAtomicClock L D x a κ) p

theorem reflectedAtomicLifetime_eq_attainment_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    reflectedAtomicLifetime L D x a κ =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
      reflectedAtomicAttainmentLifetime L D x a κ :=
  contactLifetime_eq_attainment_ae brownianDyadicMeasure (reflectedAtomicClock L D x a κ)
    (fun t _ => reflectedAtomicClock_measurable L D x a κ t)
    ((reflectedAtomicClock_paths_ae L hL D hD x a κ hκ).mono (fun _ hp => hp.2))

theorem reflectedAtomicLifetimeValue_eq_attainment_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    reflectedAtomicLifetimeValue L D x a κ =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
      reflectedAtomicAttainmentLifetimeValue L D x a κ :=
  contactLifetimeValue_eq_attainment_ae brownianDyadicMeasure (reflectedAtomicClock L D x a κ)
    (fun t _ => reflectedAtomicClock_measurable L D x a κ t)
    ((reflectedAtomicClock_paths_ae L hL D hD x a κ hκ).mono (fun _ hp => hp.2))

theorem reflectedAtomicAttainmentLifetimeValue_aemeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    AEMeasurable (reflectedAtomicAttainmentLifetimeValue L D x a κ)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  (reflectedAtomicLifetimeValue_aemeasurable L hL D hD x a κ hκ).congr
    (reflectedAtomicLifetimeValue_eq_attainment_ae L hL D hD x a κ hκ)

theorem reflectedAtomicAttainmentLifetime_survival_iff_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      (t : WithTop ℝ) < reflectedAtomicAttainmentLifetime L D x a κ p ↔
        reflectedAtomicClock L D x a κ t p.1 < p.2 := by
  filter_upwards [reflectedAtomicLifetime_eq_attainment_ae L hL D hD x a κ hκ,
    reflectedAtomicLifetime_survival_iff_ae L hL D hD x a κ hκ t ht] with p he hs
  rwa [← he]

theorem reflectedAtomicAttainmentLifetime_survival_probability (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialKillingMeasure brownianDyadicMeasure
      {p | (t : WithTop ℝ) < reflectedAtomicAttainmentLifetime L D x a κ p} =
      ENNReal.ofReal (reflectedAtomicMeanSurvival L D x a κ t.toNNReal) := by
  have he : {p | (t : WithTop ℝ) < reflectedAtomicAttainmentLifetime L D x a κ p}
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        {p | (t : WithTop ℝ) < reflectedAtomicLifetime L D x a κ p} := by
    apply eventuallyEq_set.mpr
    filter_upwards [reflectedAtomicLifetime_eq_attainment_ae L hL D hD x a κ hκ] with p hp
    rw [hp]
  exact (measure_congr he).trans
    (reflectedAtomicLifetime_survival_probability L hL D hD x a κ hκ t ht)

theorem reflectedAtomicAttainmentLifetimeValue_mean_survival (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, reflectedAtomicAttainmentLifetimeValue L D x a κ p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (reflectedAtomicMeanSurvival L D x a κ r.toNNReal) :=
  (lintegral_congr_ae (reflectedAtomicLifetimeValue_eq_attainment_ae L hL D hD x a κ hκ).symm).trans
    (reflectedAtomicLifetimeValue_mean_survival L hL D hD x a κ hκ)

theorem reflectedAtomicAttainmentLifetimeValue_mean_identity (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, reflectedAtomicAttainmentLifetimeValue L D x a κ p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (reflectedAtomicSurvival L D x a κ r.toNNReal ω)) ∂brownianDyadicMeasure :=
  (lintegral_congr_ae (reflectedAtomicLifetimeValue_eq_attainment_ae L hL D hD x a κ hκ).symm).trans
    (reflectedAtomicLifetimeValue_mean_identity L hL D hD x a κ hκ)

end TimeTraps.Probability
