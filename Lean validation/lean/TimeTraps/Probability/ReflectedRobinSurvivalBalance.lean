module

public import TimeTraps.Probability.ReflectedRobinHazardMeasure
public import TimeTraps.Probability.ReflectedRobinHazardPaths
public import TimeTraps.Probability.ReflectedAtomicHazardBalance

@[expose] public section

/-! The actual combined Robin survival has its exact finite-horizon
hazard balance. Interior and endpoint reactions remain in the same
clock, and the finite interior family may be empty. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reflectedRobinHazard_survival_balance_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      IntegrableOn (fun r => reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω)
        (Ioc (0 : ℝ) T.val) (reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) ∧
      (∫ r in Ioc (0 : ℝ) T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω
        ∂reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) =
        1 - reflectedRobinSurvival L D x a κ β₀ βL T ω ∧
      0 ≤ (∫ r in Ioc (0 : ℝ) T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω
        ∂reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) ∧
      (∫ r in Ioc (0 : ℝ) T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω
        ∂reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) ≤ 1 := by
  simp only [reflectedRobinSurvival_eq_atomic L hD, reflectedRobinHazardTimeMeasure]
  exact reflectedAtomicHazard_survival_balance_ae L hL D hD x
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
    (reflectedRobinStrength_nonneg hκ hβ₀ hβL)

end TimeTraps.Probability
