module

public import TimeTraps.Probability.ReversibleResistanceMeanLifetimeReference

@[expose] public section

/-! The physical lifetime is almost surely finite, and its actual real
value equals the reference clock cost before killing. Reference finiteness
has already been derived from spectral survival; no finiteness premise
is added to the time-change construction. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reversibleResistanceAttainmentLifetime_ne_top (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetime D.medium x D.site κ p ≠ ⊤ := by
  filter_upwards [reversibleResistanceAttainmentLifetime_clock_product_ae D.medium x D.site κ,
    reversibleResistanceReferenceLifetime_ne_top D hn κ hκ hx] with p hc hf
  intro ht
  exact hf ((positiveClockLifetimeMap_eq_top_iff _ _).mp (hc.symm.trans ht))

theorem reversibleResistanceAttainmentLifetimeValue_lt_top (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p < ∞ := by
  filter_upwards [reversibleResistanceAttainmentLifetime_ne_top D hn κ hκ hx] with p hp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hp
  change nonnegativeLifetimeValue (reversibleResistanceAttainmentLifetime D.medium x D.site κ p) < ∞
  rw [← ht, nonnegativeLifetimeValue_coe]
  exact ENNReal.ofReal_lt_top

theorem reversibleResistanceAttainmentLifetimeValue_cost_ae (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    (fun p => (reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p).toReal)
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        reversibleResistanceReferenceLifetimeCost D κ x := by
  filter_upwards [reversibleResistanceAttainmentLifetime_clock_product_ae D.medium x D.site κ,
    reversibleResistanceReferenceLifetime_ne_top D hn κ hκ hx] with p hc hf
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hf
  have ht0 : 0 ≤ t := by
    have hn : (0 : WithTop ℝ) ≤ reflectedAtomicAttainmentLifetime D.medium.resistanceLength
        1 (D.medium.resistance x) (fun i => D.medium.resistance (D.site i)) κ p :=
      attainmentKillingTime_nonneg _ _
    rw [← ht] at hn
    exact WithTop.coe_le_coe.mp hn
  have hcost : reversibleResistanceReferenceLifetimeCost D κ x p =
      ∫ r in (0 : ℝ)..t,
        D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1) := by
    unfold reversibleResistanceReferenceLifetimeCost
    rw [← ht]
    have hs : {r : ℝ | 0 < r ∧ (r : WithTop ℝ) < (t : WithTop ℝ)} = Ioo 0 t :=
      Set.ext (fun _ => and_congr Iff.rfl WithTop.coe_lt_coe)
    rw [hs, intervalIntegral.integral_of_le ht0, integral_Ioc_eq_integral_Ioo]
  rw [← ht, positiveClockLifetimeMap_coe] at hc
  change (nonnegativeLifetimeValue
    (reversibleResistanceAttainmentLifetime D.medium x D.site κ p)).toReal = _
  rw [hc, nonnegativeLifetimeValue_coe,
    ENNReal.toReal_ofReal (reversibleResistanceClock D.medium x t.toNNReal p.1).coe_nonneg,
    reversibleResistanceClock_coe]
  calc
    _ = ∫ r in (0 : ℝ)..t,
        D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1) :=
      congrArg (fun b : ℝ => ∫ r in (0 : ℝ)..b,
        D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1))
        (Real.coe_toNNReal t ht0)
    _ = _ := hcost.symm

theorem reversibleResistanceAttainmentLifetimeValue_integrable (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    Integrable (fun p => (reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  (reversibleResistanceReferenceLifetimeCost_integrable D hn κ hκ hx).congr
    (reversibleResistanceAttainmentLifetimeValue_cost_ae D hn κ hκ hx).symm

end TimeTraps.Probability
