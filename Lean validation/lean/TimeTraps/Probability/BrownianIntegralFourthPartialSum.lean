module

public import TimeTraps.Probability.BrownianIntegralFourthUpdate

@[expose] public section

/-! Actual finite stochastic sums on a nondecreasing deterministic grid.
Fourth integrability and the sampled-filtration martingale are derived
from the Gaussian update, before any energy estimate is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianFourthPartialSum (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0)
    (ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => brownianFourthPartialSum B τ ξ n ω + ξ n ω * (B (τ (n + 1)) ω - B (τ n) ω)

def brownianFourthGridFiltration (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t))
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) : Filtration ℕ mΩ where
  seq n := brownianNaturalFiltration B hBm (τ n)
  mono' := fun _ _ hij => (brownianNaturalFiltration B hBm).mono (hτ hij)
  le' n := (brownianNaturalFiltration B hBm).le (τ n)

theorem brownianFourthPartialSum_stronglyAdapted (hBm : ∀ t, Measurable (B t))
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ n, StronglyMeasurable[brownianNaturalFiltration B hBm (τ n)] (ξ n)) :
    StronglyAdapted (brownianFourthGridFiltration B hBm τ hτ) (brownianFourthPartialSum B τ ξ) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    have hm := (brownianNaturalFiltration B hBm).mono (hτ (Nat.le_succ n))
    exact (ih.mono hm).add (((hξ n).mono hm).mul
      ((brownianNaturalFiltration_stronglyAdapted B hBm (τ (n + 1))).sub
        ((brownianNaturalFiltration_stronglyAdapted B hBm (τ n)).mono hm)))

theorem brownianFourthPartialSum_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ n, StronglyMeasurable[brownianNaturalFiltration B hBm (τ n)] (ξ n))
    (hξ4 : ∀ n, MemLp (ξ n) 4 P) (n : ℕ) : MemLp (brownianFourthPartialSum B τ ξ n) 4 P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero => exact memLp_const 0
  | succ n ih =>
    exact brownian_fourth_update_memLp hB hBm (hτ (Nat.le_succ n))
      (brownianFourthPartialSum_stronglyAdapted hBm τ hτ ξ hξ n) (hξ n) ih (hξ4 n)

theorem brownianFourthPartialSum_martingale (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ n, StronglyMeasurable[brownianNaturalFiltration B hBm (τ n)] (ξ n))
    (hξ4 : ∀ n, MemLp (ξ n) 4 P) :
    Martingale (brownianFourthPartialSum B τ ξ) (brownianFourthGridFiltration B hBm τ hτ) P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmem := brownianFourthPartialSum_memLp hB hBm τ hτ ξ hξ hξ4
  have had := brownianFourthPartialSum_stronglyAdapted hBm τ hτ ξ hξ
  apply martingale_nat had (fun n => (hmem n).integrable (by norm_num))
  intro n
  have hiξ : Integrable (ξ n) P := (hξ4 n).integrable (by norm_num)
  have hinc := brownian_weighted_increment_integrable hB hBm (hτ (Nat.le_succ n)) (hξ n) hiξ
  have hc := condExp_add ((hmem n).integrable (by norm_num)) hinc
    (brownianNaturalFiltration B hBm (τ n))
  have he := brownian_weighted_increment_condExp hB hBm (hτ (Nat.le_succ n)) (hξ n) hiξ
  rw [condExp_of_stronglyMeasurable ((brownianNaturalFiltration B hBm).le (τ n))
    (had n) ((hmem n).integrable (by norm_num))] at hc
  filter_upwards [hc, he] with ω hω hiω
  change brownianFourthPartialSum B τ ξ n ω =
    P[fun ω => brownianFourthPartialSum B τ ξ n ω + ξ n ω * (B (τ (n + 1)) ω - B (τ n) ω) |
      brownianNaturalFiltration B hBm (τ n)] ω
  change P[fun ω => brownianFourthPartialSum B τ ξ n ω + ξ n ω * (B (τ (n + 1)) ω - B (τ n) ω) |
      brownianNaturalFiltration B hBm (τ n)] ω = brownianFourthPartialSum B τ ξ n ω +
      P[fun ω => ξ n ω * (B (τ (n + 1)) ω - B (τ n) ω) | brownianNaturalFiltration B hBm (τ n)] ω at hω
  rw [hω, hiω]
  simp only [Pi.zero_apply, add_zero]

theorem brownianFourthPartialSum_fourth_recursion (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ n, StronglyMeasurable[brownianNaturalFiltration B hBm (τ n)] (ξ n))
    (hξ4 : ∀ n, MemLp (ξ n) 4 P) (n : ℕ) :
    (∫ ω, brownianFourthPartialSum B τ ξ n ω ^ 4 ∂P) =
      ∑ i ∈ Finset.range n, (6 * ((τ (i + 1)).val - (τ i).val) *
        (∫ ω, brownianFourthPartialSum B τ ξ i ω ^ 2 * ξ i ω ^ 2 ∂P) +
          3 * ((τ (i + 1)).val - (τ i).val) ^ 2 * ∫ ω, ξ i ω ^ 4 ∂P) := by
  induction n with
  | zero => simp [brownianFourthPartialSum]
  | succ n ih =>
    have hu := (brownian_fourth_update_integral hB hBm (hτ (Nat.le_succ n))
      (brownianFourthPartialSum_stronglyAdapted hBm τ hτ ξ hξ n) (hξ n)
      (brownianFourthPartialSum_memLp hB hBm τ hτ ξ hξ hξ4 n) (hξ4 n)).2
    change (∫ ω, brownianFourthPartialSum B τ ξ (n + 1) ω ^ 4 ∂P) = _ at hu
    rw [hu, ih, Finset.sum_range_succ]
    ring

end TimeTraps.Probability
