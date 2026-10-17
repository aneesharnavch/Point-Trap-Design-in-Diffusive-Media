module

public import TimeTraps.Probability.BrownianDenseRealization
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! Exact moments and tail estimates for the countable Brownian realization.
The measure is the constructed projective extension; no path continuity or
Brownian-process existence hypothesis is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem gaussianReal_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (v * t ^ 2 / 2))
      (v * t * Real.exp (v * t ^ 2 / 2)) t := by
    convert! (((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2 |>.exp using 1
    dsimp
    ring
  have h1 : deriv (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) =
      fun t => v * t * Real.exp (v * t ^ 2 / 2) := funext fun t => (hd t).deriv
  have h2 : deriv (fun t : ℝ => v * t * Real.exp (v * t ^ 2 / 2)) =
      fun t => (v + (v : ℝ) ^ 2 * t ^ 2) * Real.exp (v * t ^ 2 / 2) := by
    ext t
    convert! (((hasDerivAt_id t).const_mul (v : ℝ)).mul (hd t)).deriv using 1
    dsimp
    ring
  have h3 : deriv (fun t : ℝ => (v + (v : ℝ) ^ 2 * t ^ 2) *
      Real.exp (v * t ^ 2 / 2)) =
      fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) *
        Real.exp (v * t ^ 2 / 2) := by
    ext t
    convert! (((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ) ^ 2)).const_add
      (v : ℝ)).mul (hd t)).deriv using 1
    dsimp
    ring
  have h4 : deriv (fun t : ℝ => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) *
      Real.exp (v * t ^ 2 / 2)) 0 = 3 * (v : ℝ) ^ 2 := by
    convert! (((hasDerivAt_id (0 : ℝ)).const_mul (3 * (v : ℝ) ^ 2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ) ^ 3))).mul (hd 0)
      |>.deriv using 1
    simp
  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) =
        iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero (by simp)]
      rfl
    _ = 3 * (v : ℝ) ^ 2 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rw [iteratedDeriv_succ (n := 3), iteratedDeriv_succ (n := 2),
        iteratedDeriv_succ (n := 1), iteratedDeriv_one, h1, h2, h3, h4]

theorem brownianSequence_increment_subGaussian (τ : ℕ → ℝ≥0) (n m : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℝ => ω n - ω m)
      (nndist (τ n).val (τ m).val) (brownianSequenceMeasure τ) where
  integrable_exp_mul t := by
    rw [← mgf_pos_iff, mgf_gaussianReal (brownianSequence_increment_hasLaw τ n m).map_eq]
    exact Real.exp_pos _
  mgf_le t := by
    rw [mgf_gaussianReal (brownianSequence_increment_hasLaw τ n m).map_eq]
    simp

theorem brownianSequence_increment_integrable_pow (τ : ℕ → ℝ≥0) (n m k : ℕ) :
    Integrable (fun ω : ℕ → ℝ => (ω n - ω m) ^ k) (brownianSequenceMeasure τ) := by
  apply integrable_pow_of_mem_interior_integrableExpSet
  simp [(brownianSequence_increment_subGaussian τ n m).integrableExpSet_eq_univ]

theorem brownianSequence_increment_fourth_moment (τ : ℕ → ℝ≥0) (n m : ℕ) :
    (∫ ω : ℕ → ℝ, (ω n - ω m) ^ 4 ∂brownianSequenceMeasure τ) =
      3 * |(τ n).val - (τ m).val| ^ 2 := by
  calc
    _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 (nndist (τ n).val (τ m).val) :=
      (brownianSequence_increment_hasLaw τ n m).integral_comp (by fun_prop)
    _ = 3 * (nndist (τ n).val (τ m).val : ℝ) ^ 2 := gaussianReal_fourth_moment _
    _ = _ := by
      change 3 * (dist (τ n).val (τ m).val) ^ 2 = _
      rw [Real.dist_eq]

theorem brownianSequence_increment_tail (τ : ℕ → ℝ≥0) (n m : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (brownianSequenceMeasure τ).real {ω | ε ≤ |ω n - ω m|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * |(τ n).val - (τ m).val|)) := by
  have h₁ := (brownianSequence_increment_subGaussian τ n m).measure_ge_le hε
  have h₂ := (brownianSequence_increment_subGaussian τ m n).measure_ge_le hε
  change (brownianSequenceMeasure τ).real {ω | ε ≤ ω n - ω m} ≤
    Real.exp (-ε ^ 2 / (2 * dist (τ n).val (τ m).val)) at h₁
  change (brownianSequenceMeasure τ).real {ω | ε ≤ ω m - ω n} ≤
    Real.exp (-ε ^ 2 / (2 * dist (τ m).val (τ n).val)) at h₂
  rw [dist_comm (τ m).val (τ n).val] at h₂
  simp only [Real.dist_eq] at h₁ h₂
  have he : {ω : ℕ → ℝ | ε ≤ |ω n - ω m|} =
      {ω | ε ≤ ω n - ω m} ∪ {ω | ε ≤ ω m - ω n} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, le_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [he]
  exact (measureReal_union_le _ _).trans (by linarith)

theorem brownianSequence_increment_tail_fourth (τ : ℕ → ℝ≥0) (n m : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    (brownianSequenceMeasure τ).real {ω | ε ≤ |ω n - ω m|} ≤
      3 * |(τ n).val - (τ m).val| ^ 2 / ε ^ 4 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := brownianSequenceMeasure τ) (f := fun ω : ℕ → ℝ => (ω n - ω m) ^ 4)
    (Filter.Eventually.of_forall (fun _ => by positivity))
    (brownianSequence_increment_integrable_pow τ n m 4) (ε ^ 4)
  rw [brownianSequence_increment_fourth_moment] at h
  have he : {ω : ℕ → ℝ | ε ^ 4 ≤ (ω n - ω m) ^ 4} =
      {ω | ε ≤ |ω n - ω m|} := by
    ext ω
    rw [mem_ofPred_eq, mem_ofPred_eq, ← show |ω n - ω m| ^ 4 = (ω n - ω m) ^ 4
      from (by norm_num : Even (4 : ℕ)).pow_abs _]
    exact pow_le_pow_iff_left₀ hε.le (abs_nonneg _) (by norm_num)
  rw [he] at h
  exact (le_div_iff₀ (pow_pos hε 4)).mpr (by simpa [mul_comm] using h)

end TimeTraps.Probability
