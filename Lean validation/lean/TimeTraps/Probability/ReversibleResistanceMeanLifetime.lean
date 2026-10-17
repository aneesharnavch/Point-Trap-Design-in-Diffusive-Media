module

public import TimeTraps.Probability.ReversibleResistanceMeanLifetimeData

@[expose] public section

/-! The actual mean first-attainment lifetime of the constructed
variable-medium diffusion is exactly every original physical weak mean
state. Almost-sure finiteness, ordinary integrability and the extended
mean are conclusions, with the original coefficients and trap strengths. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {n : ℕ}

def reversibleResistanceMeanLifetime {ι : Type*} [Fintype ι] (A : IntervalMedium)
    (x : ℝ) (a κ : ι → ℝ) : ℝ :=
  ∫ p, (reversibleResistanceAttainmentLifetimeValue A x a κ p).toReal
    ∂exponentialKillingMeasure brownianDyadicMeasure

theorem reversibleResistanceMeanLifetime_eq {D : OrderedMedium n} (hn : 0 < n)
    {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ} (hu : WeakIntervalEquation D κ u)
    {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    reversibleResistanceMeanLifetime D.medium x D.site κ = u x :=
  (integral_congr_ae (reversibleResistanceAttainmentLifetimeValue_cost_ae D hn κ hκ hx)).trans
    (reversibleResistanceReferenceLifetimeCost_expected D hn κ hκ hu hx)

theorem reversibleResistanceMeanLifetime_eqOn {D : OrderedMedium n} (hn : 0 < n)
    {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ} (hu : WeakIntervalEquation D κ u) :
    EqOn (fun x => reversibleResistanceMeanLifetime D.medium x D.site κ) u
      (Icc D.source.left D.source.right) :=
  fun _ hx => reversibleResistanceMeanLifetime_eq hn hκ hu hx

theorem reversibleResistanceMeanLifetime_weak_equation (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) :
    WeakIntervalEquation D κ (fun x => reversibleResistanceMeanLifetime D.medium x D.site κ) :=
  (D.resistanceMeanState_weak hn κ hκ).congr_state
    (reversibleResistanceMeanLifetime_eqOn hn hκ (D.resistanceMeanState_weak hn κ hκ)).symm

theorem reversibleResistanceMeanLifetime_finite {D : OrderedMedium n} (hn : 0 < n)
    {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ} (hu : WeakIntervalEquation D κ u)
    {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    (∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p < ∞) ∧
    Integrable (fun p => (reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) ∧
    (∫ p, (reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p).toReal
      ∂exponentialKillingMeasure brownianDyadicMeasure) = u x :=
  ⟨reversibleResistanceAttainmentLifetimeValue_lt_top D hn κ hκ hx,
    reversibleResistanceAttainmentLifetimeValue_integrable D hn κ hκ hx,
      reversibleResistanceMeanLifetime_eq hn hκ hu hx⟩

theorem reversibleResistanceMeanLifetime_value_aemeasurable (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    AEMeasurable (reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ)
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  apply (reversibleResistanceAttainmentLifetimeValue_integrable D hn κ hκ hx).aestronglyMeasurable.aemeasurable.ennreal_ofReal.congr
  filter_upwards [reversibleResistanceAttainmentLifetimeValue_lt_top D hn κ hκ hx] with p hp
  exact ENNReal.ofReal_toReal hp.ne

theorem reversibleResistanceMeanLifetime_extended_mean {D : OrderedMedium n} (hn : 0 < n)
    {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ} (hu : WeakIntervalEquation D κ u)
    {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    (∫⁻ p, reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p
      ∂exponentialKillingMeasure brownianDyadicMeasure) = ENNReal.ofReal (u x) := by
  calc
    _ = ∫⁻ p, ENNReal.ofReal
        ((reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p).toReal)
        ∂exponentialKillingMeasure brownianDyadicMeasure := by
      apply lintegral_congr_ae
      filter_upwards [reversibleResistanceAttainmentLifetimeValue_lt_top D hn κ hκ hx] with p hp
      exact (ENNReal.ofReal_toReal hp.ne).symm
    _ = ENNReal.ofReal (reversibleResistanceMeanLifetime D.medium x D.site κ) :=
      (ofReal_integral_eq_lintegral_ofReal
        (reversibleResistanceAttainmentLifetimeValue_integrable D hn κ hκ hx)
        (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))).symm
    _ = _ := congrArg ENNReal.ofReal (reversibleResistanceMeanLifetime_eq hn hκ hu hx)

end TimeTraps.Probability

end
