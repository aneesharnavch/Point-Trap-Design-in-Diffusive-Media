module

public import TimeTraps.Analysis.IntervalLinearPairUniqueness
public import TimeTraps.Analysis.IntervalFluxRegularity

@[expose] public section

/-! Cauchy uniqueness for the original divergence-form Sturm system
u' = j / p and j' = c u, with continuous positive p and continuous c.
The coefficient p is never differentiated. The Cauchy point may be either
endpoint or any interior point. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem intervalEnergy_sturm_eq_zero_of_cauchy
    {u j p c : ℝ → ℝ} {a b t₀ : ℝ}
    (hu : IntervalEnergy u a b) (hj : IntervalEnergy j a b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < p x)
    (hc : ContinuousOn c (Icc a b))
    (hdu : deriv u =ᵐ[volume.restrict (Ioo a b)] (fun x => j x / p x))
    (hdj : deriv j =ᵐ[volume.restrict (Ioo a b)] (fun x => c x * u x))
    (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b) (hu₀ : u t₀ = 0) (hj₀ : j t₀ = 0) :
    ∀ x ∈ Icc a b, u x = 0 ∧ j x = 0 := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    have ht : t₀ = a := le_antisymm ht₀.2 ht₀.1
    subst t₀
    intro x hx
    have hxa : x = a := le_antisymm hx.2 hx.1
    simpa only [hxa] using And.intro hu₀ hj₀
  · apply intervalEnergy_pair_eq_zero_of_cauchy hu hj
      (hp.inv₀ (fun x hx => (hpos x hx).ne')) hc _ hdj hlt ht₀ hu₀ hj₀
    filter_upwards [hdu] with x hx
    simpa only [div_eq_mul_inv, Pi.inv_apply, mul_comm] using hx

theorem IntervalFluxRegularity.eq_zero_of_linear_cauchy
    {u j p c : ℝ → ℝ} {a b t₀ : ℝ}
    (h : IntervalFluxRegularity u j (fun x => c x * u x) p a b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < p x)
    (hc : ContinuousOn c (Icc a b)) (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hu₀ : u t₀ = 0) (hj₀ : j t₀ = 0) :
    ∀ x ∈ Icc a b, u x = 0 ∧ j x = 0 :=
  intervalEnergy_sturm_eq_zero_of_cauchy h.state_energy h.flux_energy hp hpos hc
    (h.derivative_ae (fun x hx => (hpos x hx).ne')) h.source_ae hab ht₀ hu₀ hj₀

end TimeTraps.Analysis
