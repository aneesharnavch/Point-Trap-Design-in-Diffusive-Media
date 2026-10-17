module

public import TimeTraps.Probability.BrownianIntegralFourthEnergyPath

@[expose] public section

/-! The genuine finite Gaussian stochastic sum satisfies the fourth-moment
energy bound with constant 150, and its finite running maximum with 600.
All coefficients may be unbounded adapted L4 random variables. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFourthEnergy_memLp (τ : ℕ → ℝ≥0) (ξ : ℕ → Ω → ℝ)
    (hξ4 : ∀ i, MemLp (ξ i) 4 P) (n : ℕ) : MemLp (brownianFourthEnergy τ ξ n) 2 P :=
  memLp_finsetSum _ (fun i _ => (brownian_fourth_square_memLp (hξ4 i)).const_mul _)

theorem brownian_fourth_running_square_memLp {M : ℕ → Ω → ℝ}
    (hM : ∀ i, MemLp (M i) 4 P) (n : ℕ) :
    MemLp (fun ω => (finiteRunningMax (fun i => |M i ω|) n) ^ 2) 2 P := by
  have hi := finiteRunningMax_memLp (fun i => brownian_fourth_square_memLp (hM i)) n
  have he : (fun ω => finiteRunningMax (fun i => M i ω ^ 2) n) =
      fun ω => (finiteRunningMax (fun i => |M i ω|) n) ^ 2 := by
    funext ω
    simpa only [sq_abs] using finiteRunningMax_square_of_nonneg (fun i => |M i ω|) (fun i => abs_nonneg _) n
  rwa [he] at hi

theorem brownianFourthPartialSum_energy_pairing (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ n, StronglyMeasurable[brownianNaturalFiltration B hBm (τ n)] (ξ n))
    (hξ4 : ∀ n, MemLp (ξ n) 4 P) (n : ℕ) :
    (∫ ω, brownianFourthPartialSum B τ ξ n ω ^ 4 ∂P) ≤
      6 * (∫ ω, (finiteRunningMax (fun i => |brownianFourthPartialSum B τ ξ i ω|) n) ^ 2 *
        brownianFourthEnergy τ ξ n ω ∂P) + 3 * ∫ ω, brownianFourthEnergy τ ξ n ω ^ 2 ∂P := by
  let M := brownianFourthPartialSum B τ ξ
  have hM := brownianFourthPartialSum_memLp hB hBm τ hτ ξ hξ hξ4
  have hmix (i : ℕ) : Integrable (fun ω => M i ω ^ 2 * ξ i ω ^ 2) P :=
    (brownian_fourth_mixed_integrable (hM i) (hξ4 i)).2.1
  have hpow (i : ℕ) : Integrable (fun ω => ξ i ω ^ 4) P := brownian_memLp_four_integrable_fourth (hξ4 i)
  let F : ℕ → Ω → ℝ := fun i ω => 6 * ((τ (i + 1)).val - (τ i).val) *
    (M i ω ^ 2 * ξ i ω ^ 2) + 3 * ((τ (i + 1)).val - (τ i).val) ^ 2 * ξ i ω ^ 4
  have hiF (i : ℕ) : Integrable (F i) P :=
    ((hmix i).const_mul _).add ((hpow i).const_mul _)
  have hR2 := brownian_fourth_running_square_memLp hM n
  have hA2 := brownianFourthEnergy_memLp τ ξ hξ4 n
  have hiRA : Integrable (fun ω => (finiteRunningMax (fun i => |M i ω|) n) ^ 2 *
      brownianFourthEnergy τ ξ n ω) P := hR2.integrable_mul hA2
  calc
    _ = ∫ ω, ∑ i ∈ Finset.range n, F i ω ∂P := by
      rw [brownianFourthPartialSum_fourth_recursion hB hBm τ hτ ξ hξ hξ4 n,
        integral_finsetSum _ (fun i _ => hiF i)]
      apply Finset.sum_congr rfl
      intro i _
      change _ = ∫ ω, 6 * ((τ (i + 1)).val - (τ i).val) * (M i ω ^ 2 * ξ i ω ^ 2) +
        3 * ((τ (i + 1)).val - (τ i).val) ^ 2 * ξ i ω ^ 4 ∂P
      rw [integral_add ((hmix i).const_mul _) ((hpow i).const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ ∫ ω, 6 * ((finiteRunningMax (fun i => |M i ω|) n) ^ 2 * brownianFourthEnergy τ ξ n ω) +
        3 * brownianFourthEnergy τ ξ n ω ^ 2 ∂P := by
      apply integral_mono (integrable_finsetSum _ (fun i _ => hiF i))
        ((hiRA.const_mul 6).add (hA2.integrable_sq.const_mul 3))
      exact fun ω => brownian_fourth_energy_path_bound τ hτ M ξ n ω
    _ = _ := by
      rw [integral_add (hiRA.const_mul 6) (hA2.integrable_sq.const_mul 3), integral_const_mul, integral_const_mul]

theorem brownianFourthPartialSum_energy_bound (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ n, StronglyMeasurable[brownianNaturalFiltration B hBm (τ n)] (ξ n))
    (hξ4 : ∀ n, MemLp (ξ n) 4 P) (n : ℕ) :
    (∫ ω, brownianFourthPartialSum B τ ξ n ω ^ 4 ∂P) ≤
      150 * ∫ ω, brownianFourthEnergy τ ξ n ω ^ 2 ∂P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let M := brownianFourthPartialSum B τ ξ
  let R : Ω → ℝ := fun ω => (finiteRunningMax (fun i => |M i ω|) n) ^ 2
  let A := brownianFourthEnergy τ ξ n
  have hM := brownianFourthPartialSum_memLp hB hBm τ hτ ξ hξ hξ4
  have hR2 : MemLp R 2 P := brownian_fourth_running_square_memLp hM n
  have hA2 : MemLp A 2 P := brownianFourthEnergy_memLp τ ξ hξ4 n
  have hmax := brownian_fourth_martingale_maximal
    (brownianFourthPartialSum_martingale hB hBm τ hτ ξ hξ hξ4) hM n
  have hRq : (∫ ω, R ω ^ 2 ∂P) ≤ 4 * ∫ ω, M n ω ^ 4 ∂P := by
    simpa only [R, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hmax
  have hE : 0 ≤ ∫ ω, A ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  apply brownian_fourth_energy_scalar_bound
    (integral_nonneg (fun ω => by dsimp [M]; positivity))
    (integral_nonneg (fun ω => mul_nonneg (sq_nonneg _) (brownianFourthEnergy_nonneg τ hτ ξ n ω))) hE
    (brownianFourthPartialSum_energy_pairing hB hBm τ hτ ξ hξ hξ4 n)
  exact (memLp_integral_mul_sq_le hR2 hA2).trans (mul_le_mul_of_nonneg_right hRq hE)

theorem brownianFourthPartialSum_maximal_energy_bound (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ n, StronglyMeasurable[brownianNaturalFiltration B hBm (τ n)] (ξ n))
    (hξ4 : ∀ n, MemLp (ξ n) 4 P) (n : ℕ) :
    (∫ ω, finiteRunningMax (fun i => |brownianFourthPartialSum B τ ξ i ω|) n ^ 4 ∂P) ≤
      600 * ∫ ω, brownianFourthEnergy τ ξ n ω ^ 2 ∂P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmax := brownian_fourth_martingale_maximal
    (brownianFourthPartialSum_martingale hB hBm τ hτ ξ hξ hξ4)
    (brownianFourthPartialSum_memLp hB hBm τ hτ ξ hξ hξ4) n
  have hb := brownianFourthPartialSum_energy_bound hB hBm τ hτ ξ hξ hξ4 n
  linarith

end TimeTraps.Probability
