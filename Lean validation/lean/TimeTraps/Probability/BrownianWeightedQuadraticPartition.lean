module

public import TimeTraps.Probability.BrownianWeightedQuadraticWeight
public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-! Exact finite-partition orthogonality and second moments for weighted
compensated quadratic variation. Coefficients may be signed and depend
on the entire earlier raw filtration; empty and repeated-time grids are
included. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianWeightedQuadraticSum (B : ℝ≥0 → Ω → ℝ) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin N, ξ i ω * brownianCompensatedSquareIncrement B (τ i.castSucc) (τ i.succ) ω

theorem brownianWeightedQuadraticSum_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) : MemLp (brownianWeightedQuadraticSum B τ ξ) 2 P :=
  memLp_finsetSum _ (fun i _ => brownian_weightedQuadratic_memLp hB hBm
    (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i))

theorem brownianWeightedQuadraticSum_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) :
    (∫ ω, brownianWeightedQuadraticSum B τ ξ ω ∂P) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∑ i : Fin N, ∫ ω, ξ i ω * brownianCompensatedSquareIncrement B (τ i.castSucc) (τ i.succ) ω ∂P :=
      integral_finsetSum _ (fun i _ => brownian_weightedQuadratic_integrable hB hBm
        (hτ (Fin.castSucc_le_succ i)) (hξ i) ((hξ2 i).integrable (by norm_num)))
    _ = ∑ _ : Fin N, (0 : ℝ) := Finset.sum_congr rfl (fun i _ =>
      brownian_weightedQuadratic_mean hB hBm (hτ (Fin.castSucc_le_succ i))
        (hξ i) ((hξ2 i).integrable (by norm_num)))
    _ = 0 := Finset.sum_const_zero

theorem brownianWeightedQuadratic_terms_orthogonal (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) {i j : Fin N} (hij : i ≠ j) :
    (∫ ω, (ξ i ω * brownianCompensatedSquareIncrement B (τ i.castSucc) (τ i.succ) ω) *
      (ξ j ω * brownianCompensatedSquareIncrement B (τ j.castSucc) (τ j.succ) ω) ∂P) = 0 := by
  suffices hlt : ∀ i j : Fin N, i < j →
      (∫ ω, (ξ i ω * brownianCompensatedSquareIncrement B (τ i.castSucc) (τ i.succ) ω) *
        (ξ j ω * brownianCompensatedSquareIncrement B (τ j.castSucc) (τ j.succ) ω) ∂P) = 0 by
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact hlt i j hij'
    · simpa only [mul_comm] using hlt j i hji'
  intro i j hij'
  have hleft : τ i.castSucc ≤ τ j.castSucc := hτ (by
    change i.val ≤ j.val
    exact Nat.le_of_lt hij')
  have hright : τ i.succ ≤ τ j.castSucc := hτ (by
    change i.val + 1 ≤ j.val
    exact hij')
  have hl := (brownianNaturalFiltration B hBm).mono hleft
  have hr := (brownianNaturalFiltration B hBm).mono hright
  have hterm : StronglyMeasurable[brownianNaturalFiltration B hBm (τ j.castSucc)]
      (fun ω => ξ i ω * brownianCompensatedSquareIncrement B (τ i.castSucc) (τ i.succ) ω) :=
    ((hξ i).mono hl).mul
      ((((brownianNaturalFiltration_stronglyAdapted B hBm (τ i.succ)).mono hr).sub
        ((brownianNaturalFiltration_stronglyAdapted B hBm (τ i.castSucc)).mono hl)).pow 2 |>.sub
          stronglyMeasurable_const)
  exact brownian_weightedQuadratic_orthogonal hB hBm (hτ (Fin.castSucc_le_succ j)) hterm (hξ j)
    (brownian_weightedQuadratic_memLp hB hBm (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i)) (hξ2 j)

theorem brownianWeightedQuadraticSum_secondMoment (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) :
    (∫ ω, brownianWeightedQuadraticSum B τ ξ ω ^ 2 ∂P) =
      ∑ i : Fin N, 2 * ((τ i.succ).val - (τ i.castSucc).val) ^ 2 * ∫ ω, ξ i ω ^ 2 ∂P := by
  let Y : Fin N → Ω → ℝ := fun i ω =>
    ξ i ω * brownianCompensatedSquareIncrement B (τ i.castSucc) (τ i.succ) ω
  have hY2 : ∀ i, MemLp (Y i) 2 P := fun i =>
    brownian_weightedQuadratic_memLp hB hBm (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i)
  have hYY : ∀ i j, Integrable (fun ω => Y i ω * Y j ω) P := fun i j => (hY2 i).integrable_mul (hY2 j)
  have hdiag : ∀ i, (∑ j : Fin N, ∫ ω, Y i ω * Y j ω ∂P) = ∫ ω, Y i ω ^ 2 ∂P := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp only [pow_two]
    · intro j _ hji
      exact brownianWeightedQuadratic_terms_orthogonal hB hBm τ hτ ξ hξ hξ2 hji.symm
    · simp
  calc
    _ = ∫ ω, ∑ i : Fin N, ∑ j : Fin N, Y i ω * Y j ω ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω =>
        (pow_two (∑ i : Fin N, Y i ω)).trans (Fintype.sum_mul_sum _ _))
    _ = ∑ i : Fin N, ∑ j : Fin N, ∫ ω, Y i ω * Y j ω ∂P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hYY i j))]
      exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hYY i j))
    _ = ∑ i : Fin N, ∫ ω, Y i ω ^ 2 ∂P := Finset.sum_congr rfl (fun i _ => hdiag i)
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      brownian_weightedQuadratic_secondMoment hB hBm (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i))


end TimeTraps.Probability
