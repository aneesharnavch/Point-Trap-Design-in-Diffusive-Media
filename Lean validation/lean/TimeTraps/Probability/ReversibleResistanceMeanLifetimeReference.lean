module

public import TimeTraps.Interval.ReversibleResistanceWeakSolution
public import TimeTraps.Probability.ReflectedForcedRunningCostStopping
public import TimeTraps.Probability.ReflectedForcedRunningCostLifetime
public import TimeTraps.Probability.ReversibleResistanceLifetimeTimeChange

@[expose] public section

/-! The physical clock accumulated before reference killing has an
integrable cost whose expectation equals any original full-H1 mean
solution. The reference problem is the actual resistance transform with
unchanged contact strengths; its lifetime is proved finite. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

def reversibleResistanceReferenceLifetimeCost (D : OrderedMedium n)
    (κ : Fin n → ℝ) (x : ℝ) (p : (ℕ → ℝ) × ℝ) : ℝ :=
  ∫ r in {r : ℝ | 0 < r ∧ (r : WithTop ℝ) <
    reflectedAtomicAttainmentLifetime D.medium.resistanceLength 1 (D.medium.resistance x)
      (fun i => D.medium.resistance (D.site i)) κ p},
    D.medium.resistanceSpeed (reversibleResistanceReference D.medium x r.toNNReal p.1)

theorem reversibleResistanceReferenceLifetime_ne_top (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetime D.medium.resistanceLength 1 (D.medium.resistance x)
        (fun i => D.medium.resistance (D.site i)) κ p ≠ ⊤ :=
  reflectedForcedRunningCost_attainment_ne_top (D.resistanceSpectralProblem hn κ hκ)
    (D.medium.resistance_mem hx)

theorem reversibleResistanceReferenceLifetimeCost_nonneg (D : OrderedMedium n)
    (κ : Fin n → ℝ) (x : ℝ) (p : (ℕ → ℝ) × ℝ) :
    0 ≤ reversibleResistanceReferenceLifetimeCost D κ x p :=
  integral_nonneg (fun _ => (D.medium.resistanceSpeed_pos _).le)

theorem reversibleResistanceReferenceLifetimeCost_integrable (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    Integrable (reversibleResistanceReferenceLifetimeCost D κ x)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  reflectedForcedRunningCostStoppedValue_path_cost_integrable
    (P := D.resistanceSpectralProblem hn κ hκ)
    D.medium.resistanceSpeed_continuous.continuousOn (D.medium.resistance_mem hx)

theorem reversibleResistanceReferenceLifetimeCost_expected (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ}
    (hu : WeakIntervalEquation D κ u) {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    (∫ p, reversibleResistanceReferenceLifetimeCost D κ x p
      ∂exponentialKillingMeasure brownianDyadicMeasure) = u x := by
  have he := reflectedForcedRunningCostStoppedValue_expected_infinite
    ((D.resistanceSpectralProblem hn κ hκ).forcedSolution_weak D.medium.resistanceSpeed
      D.medium.resistanceSpeed_continuous.continuousOn)
    D.medium.resistanceSpeed_continuous.continuousOn (D.medium.resistance_mem hx)
  exact he.trans (hu.eq_resistanceMeanState hn hκ hx).symm

end TimeTraps.Probability

end
