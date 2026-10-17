module

public import TimeTraps.Probability.BrownianStepIntegralBasic

@[expose] public section

/-! Orthogonality and the exact finite Itô isometry. The cross terms vanish
by conditional expectation at the later interval's left endpoint, even
when its coefficient depends on earlier increments. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_weighted_increment_orthogonal (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {Z ξ : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hZ2 : MemLp Z 2 P) (hξ2 : MemLp ξ 2 P) :
    (∫ ω, Z ω * (ξ ω * (B t ω - B s ω)) ∂P) = 0 := by
  have h := brownian_weighted_increment_mean hB hBm hst (hZ.mul hξ)
    (hZ2.integrable_mul hξ2)
  calc
    _ = ∫ ω, (Z ω * ξ ω) * (B t ω - B s ω) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => (mul_assoc _ _ _).symm)
    _ = 0 := h

theorem brownian_step_terms_orthogonal (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) {i j : Fin N} (hij : i ≠ j) :
    (∫ ω, (ξ i ω * (B (τ i.succ) ω - B (τ i.castSucc) ω)) *
      (ξ j ω * (B (τ j.succ) ω - B (τ j.castSucc) ω)) ∂P) = 0 := by
  suffices hlt : ∀ i j : Fin N, i < j →
      (∫ ω, (ξ i ω * (B (τ i.succ) ω - B (τ i.castSucc) ω)) *
        (ξ j ω * (B (τ j.succ) ω - B (τ j.castSucc) ω)) ∂P) = 0 by
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
      (fun ω => ξ i ω * (B (τ i.succ) ω - B (τ i.castSucc) ω)) :=
    ((hξ i).mono hl).mul
      (((brownianNaturalFiltration_stronglyAdapted B hBm (τ i.succ)).mono hr).sub
        ((brownianNaturalFiltration_stronglyAdapted B hBm (τ i.castSucc)).mono hl))
  exact brownian_weighted_increment_orthogonal hB hBm (hτ (Fin.castSucc_le_succ j))
    hterm (hξ j)
    (brownian_weighted_increment_memLp hB hBm (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i))
    (hξ2 j)

theorem brownianStepIntegral_isometry (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) :
    (∫ ω, brownianStepIntegral B τ ξ ω ^ 2 ∂P) =
      ∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) * ∫ ω, ξ i ω ^ 2 ∂P := by
  let Y : Fin N → Ω → ℝ := fun i ω => ξ i ω * (B (τ i.succ) ω - B (τ i.castSucc) ω)
  have hY2 : ∀ i, MemLp (Y i) 2 P := fun i =>
    brownian_weighted_increment_memLp hB hBm (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i)
  have hYY : ∀ i j, Integrable (fun ω => Y i ω * Y j ω) P :=
    fun i j => (hY2 i).integrable_mul (hY2 j)
  have hdiag : ∀ i, (∑ j : Fin N, ∫ ω, Y i ω * Y j ω ∂P) = ∫ ω, Y i ω ^ 2 ∂P := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp only [pow_two]
    · intro j _ hji
      exact brownian_step_terms_orthogonal hB hBm τ hτ ξ hξ hξ2 hji.symm
    · simp
  calc
    _ = ∫ ω, ∑ i : Fin N, ∑ j : Fin N, Y i ω * Y j ω ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (pow_two (∑ i : Fin N, Y i ω)).trans (Fintype.sum_mul_sum _ _)
    _ = ∑ i : Fin N, ∑ j : Fin N, ∫ ω, Y i ω * Y j ω ∂P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hYY i j))]
      exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hYY i j))
    _ = ∑ i : Fin N, ∫ ω, Y i ω ^ 2 ∂P := Finset.sum_congr rfl (fun i _ => hdiag i)
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      brownian_weighted_increment_second_moment hB hBm
        (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i))

end TimeTraps.Probability
