module

public import TimeTraps.Probability.BrownianIntegralFourthEnergy
public import TimeTraps.Probability.BrownianIntegralMaximalGrid
public import TimeTraps.Probability.BrownianIntegralPartition

@[expose] public section

/-! An arbitrary finite partition is extended by repeating its final time
and using zero coefficients. Its recursive sums and energy coincide with
the original finite partition objects, including empty partitions. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianFourthExtendedCoefficient {N : ℕ} (ξ : Fin N → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  if hk : k < N then ξ ⟨k, hk⟩ else fun _ => 0

theorem brownianFourthExtendedCoefficient_at_fin {N : ℕ} (ξ : Fin N → Ω → ℝ) (i : Fin N) :
    brownianFourthExtendedCoefficient ξ i.val = ξ i := by
  simp only [brownianFourthExtendedCoefficient, dif_pos i.isLt]

theorem brownianFourthExtendedCoefficient_adapted (hBm : ∀ t, Measurable (B t))
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i)) (k : ℕ) :
    StronglyMeasurable[brownianNaturalFiltration B hBm (brownianIntegralGridTime τ k)]
      (brownianFourthExtendedCoefficient ξ k) := by
  by_cases hk : k < N
  · let i : Fin N := ⟨k, hk⟩
    have he : brownianIntegralGridTime τ k = τ i.castSucc := brownianIntegralGridTime_at_fin τ i.castSucc
    rw [he]
    simpa only [brownianFourthExtendedCoefficient, dif_pos hk] using hξ i
  · simp only [brownianFourthExtendedCoefficient, dif_neg hk]
    exact stronglyMeasurable_const

theorem brownianFourthExtendedCoefficient_memLp [IsFiniteMeasure P] {N : ℕ}
    (ξ : Fin N → Ω → ℝ) (hξ4 : ∀ i, MemLp (ξ i) 4 P) (k : ℕ) :
    MemLp (brownianFourthExtendedCoefficient ξ k) 4 P := by
  by_cases hk : k < N
  · simpa only [brownianFourthExtendedCoefficient, dif_pos hk] using hξ4 ⟨k, hk⟩
  · simpa only [brownianFourthExtendedCoefficient, dif_neg hk] using (memLp_const (μ := P) (p := 4) (0 : ℝ))

theorem brownianFourthPartialSum_sum (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0)
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    brownianFourthPartialSum B τ ξ n ω = ∑ i ∈ Finset.range n, ξ i ω * (B (τ (i + 1)) ω - B (τ i) ω) := by
  induction n with
  | zero => simp [brownianFourthPartialSum]
  | succ n ih => simp only [brownianFourthPartialSum, ih, Finset.sum_range_succ]

theorem brownianFourthPartialSum_eq_step (B : ℝ≥0 → Ω → ℝ) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ) (ω : Ω) :
    brownianFourthPartialSum B (brownianIntegralGridTime τ) (brownianFourthExtendedCoefficient ξ) N ω =
      brownianStepIntegral B τ ξ ω := by
  rw [brownianFourthPartialSum_sum, ← Fin.sum_univ_eq_sum_range]
  unfold brownianStepIntegral
  apply Finset.sum_congr rfl
  intro i _
  have hr : brownianIntegralGridTime τ (i.val + 1) = τ i.succ := brownianIntegralGridTime_at_fin τ i.succ
  have hl : brownianIntegralGridTime τ i.val = τ i.castSucc := brownianIntegralGridTime_at_fin τ i.castSucc
  rw [brownianFourthExtendedCoefficient_at_fin ξ i, hr, hl]

theorem brownianFourthEnergy_eq_partition {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ) (ω : Ω) :
    brownianFourthEnergy (brownianIntegralGridTime τ) (brownianFourthExtendedCoefficient ξ) N ω =
      ∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) * ξ i ω ^ 2 := by
  rw [brownianFourthEnergy, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hr : brownianIntegralGridTime τ (i.val + 1) = τ i.succ := brownianIntegralGridTime_at_fin τ i.succ
  have hl : brownianIntegralGridTime τ i.val = τ i.castSucc := brownianIntegralGridTime_at_fin τ i.castSucc
  rw [brownianFourthExtendedCoefficient_at_fin ξ i, hr, hl]

end TimeTraps.Probability
