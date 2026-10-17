module

public import TimeTraps.Probability.BrownianIntegralFourthIncrement
public import TimeTraps.Probability.BrownianIntegralMaximalDiscrete
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

@[expose] public section

/-! A fourth-moment Doob estimate derived by applying the already proved
L2 maximal inequality to the squared martingale. This requires actual L4
integrability; it does not assert the missing quadratic-energy estimate. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {𝒢 : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}

theorem brownian_fourth_square_memLp {ξ : Ω → ℝ} (hξ : MemLp ξ 4 P) :
    MemLp (fun ω => ξ ω ^ 2) 2 P := by
  apply (memLp_two_iff_integrable_sq (hξ.aestronglyMeasurable.pow 2)).mpr
  change Integrable (fun ω => (ξ ω ^ 2) ^ 2) P
  simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using brownian_memLp_four_integrable_fourth hξ

theorem brownian_fourth_martingale_square_submartingale (hX : Martingale X 𝒢 P)
    (hX2 : ∀ n, MemLp (X n) 2 P) : Submartingale (fun n ω => X n ω ^ 2) 𝒢 P := by
  refine ⟨fun n => (hX.stronglyMeasurable n).pow 2, ?_, fun n => (hX2 n).integrable_sq⟩
  intro i j hij
  have hi : Integrable (fun ω => ‖X j ω‖ ^ (2 : ℝ)) P := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using (hX2 j).integrable_sq
  have hc := Integrable.norm_condExp_rpow_le (f := X j) (m := 𝒢 i) (by norm_num : (1 : ℝ) ≤ 2) hi
  filter_upwards [hX.condExp_ae_eq hij, hc] with ω hω hj
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, hω] using hj

theorem finiteRunningMax_square_of_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    finiteRunningMax (fun k => f k ^ 2) n = (finiteRunningMax f n) ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finiteRunningMax, finiteRunningMax, ih]
    have hr := finiteRunningMax_nonneg f (hf 0) n
    rcases le_total (finiteRunningMax f n) (f (n + 1)) with h | h
    · rw [max_eq_right h, max_eq_right ((sq_le_sq₀ hr (hf (n + 1))).mpr h)]
    · rw [max_eq_left h, max_eq_left ((sq_le_sq₀ (hf (n + 1)) hr).mpr h)]

theorem brownian_fourth_martingale_maximal [IsFiniteMeasure P] (hX : Martingale X 𝒢 P)
    (hX4 : ∀ n, MemLp (X n) 4 P) (n : ℕ) :
    (∫ ω, finiteRunningMax (fun k => |X k ω|) n ^ 4 ∂P) ≤ 4 * ∫ ω, X n ω ^ 4 ∂P := by
  have hs := brownian_fourth_martingale_square_submartingale hX
    (fun k => (hX4 k).mono_exponent (by norm_num))
  have hb := nonnegative_submartingale_maximal_L2 hs (fun k ω => sq_nonneg (X k ω))
    (fun k => brownian_fourth_square_memLp (hX4 k)) n
  have he (ω : Ω) : finiteRunningMax (fun k => X k ω ^ 2) n =
      (finiteRunningMax (fun k => |X k ω|) n) ^ 2 := by
    simpa only [sq_abs] using finiteRunningMax_square_of_nonneg (fun k => |X k ω|) (fun k => abs_nonneg _) n
  simpa only [he, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hb

end TimeTraps.Probability
