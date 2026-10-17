module

public import TimeTraps.Probability.ReflectedRobinHazardData
public import TimeTraps.Probability.ReflectedAtomicHazardPaths
public import TimeTraps.Probability.ReflectedAtomicHazardAdapted

@[expose] public section

/-! The literal combined interior and endpoint clock is adapted,
continuous, increasing and initially zero. Its actual exponential
survival is adapted, continuous and between zero and one. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reflectedRobinHazard_nonneg (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {β₀ βL : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ reflectedRobinHazard L D x a κ β₀ βL t ω := by
  rw [reflectedRobinHazard_eq_atomic L hD]
  exact reflectedAtomicHazard_nonneg L hD x _ _ (reflectedRobinStrength_nonneg hκ hβ₀ hβL) t ω

theorem reflectedRobinSurvival_bounds (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {β₀ βL : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 < reflectedRobinSurvival L D x a κ β₀ βL t ω ∧
      reflectedRobinSurvival L D x a κ β₀ βL t ω ≤ 1 := by
  rw [reflectedRobinSurvival_eq_atomic L hD]
  exact reflectedAtomicSurvival_bounds L hD x _ _ (reflectedRobinStrength_nonneg hκ hβ₀ hβL) t ω

theorem reflectedRobinHazard_paths_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    {β₀ βL : ℝ} (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => reflectedRobinHazard L D x a κ β₀ βL t ω) ∧
      Monotone (fun t => reflectedRobinHazard L D x a κ β₀ βL t ω) ∧
      reflectedRobinHazard L D x a κ β₀ βL 0 ω = 0 ∧
      Continuous (fun t => reflectedRobinSurvival L D x a κ β₀ βL t ω) ∧
      Antitone (fun t => reflectedRobinSurvival L D x a κ β₀ βL t ω) ∧
      reflectedRobinSurvival L D x a κ β₀ βL 0 ω = 1 := by
  simp only [reflectedRobinHazard_eq_atomic L hD, reflectedRobinSurvival_eq_atomic L hD]
  exact reflectedAtomicHazard_paths_ae L hL D hD x _ _ (reflectedRobinStrength_nonneg hκ hβ₀ hβL)

theorem reflectedRobinSurvival_raw_aestronglyMeasurable (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t]
      (reflectedRobinSurvival L D x a κ β₀ βL t) brownianDyadicMeasure := by
  have he : reflectedRobinSurvival L D x a κ β₀ βL t =
      reflectedAtomicSurvival L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) t :=
    funext (reflectedRobinSurvival_eq_atomic L hD x a κ β₀ βL t)
  rw [he]
  exact reflectedAtomicSurvival_raw_aestronglyMeasurable L D x _ _ t

end TimeTraps.Probability
