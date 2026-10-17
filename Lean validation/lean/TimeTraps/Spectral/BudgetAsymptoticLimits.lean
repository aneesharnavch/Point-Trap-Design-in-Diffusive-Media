module

public import TimeTraps.Spectral.DimensionlessBudget
public import TimeTraps.Spectral.DimensionlessRootLimits
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Fixed-parameter spectral limits, identified with the attained all-placement
Rayleigh maximum. The count tends through the natural numbers; positivity is
eventual in this filter, so the limiting assertion does not shift the count. -/

namespace TimeTraps.Spectral

open Set Filter Topology

noncomputable def spectralBudgetValue (n : ℕ) (D L K : ℝ) : ℝ :=
  4 * D * (n : ℝ) ^ 2 / L ^ 2 * budgetPhase (K * L / (4 * D * (n : ℝ) ^ 2)) ^ 2

theorem BudgetProblem.zeta_eq_budgetPhase {n : ℕ} (B : BudgetProblem n) :
    B.zeta = budgetPhase (B.budget * B.length / (4 * B.diffusivity * (n : ℝ) ^ 2)) := by
  apply budgetPhase_eq_of_equation
  · exact div_pos (mul_pos B.budget_pos B.length_pos)
      (mul_pos (mul_pos (by norm_num) B.diffusivity_pos) (sq_pos_of_pos B.count_real_pos))
  · exact ⟨B.zeta_pos, B.zeta_lt⟩
  · exact B.zeta_equation

theorem BudgetProblem.spectralBudgetValue_eq {n : ℕ} (B : BudgetProblem n) :
    spectralBudgetValue n B.diffusivity B.length B.budget =
      B.diffusivity * B.uniform.root ^ 2 := by
  rw [spectralBudgetValue, ← B.zeta_eq_budgetPhase, ← B.dimensionless_value]

theorem BudgetProblem.spectralBudgetValue_maximum {n : ℕ} (B : BudgetProblem n) :
    IsGreatest B.principalValues (spectralBudgetValue n B.diffusivity B.length B.budget) := by
  rw [B.spectralBudgetValue_eq]
  exact B.joint_maximum

theorem spectralBudgetValue_ratio {n : ℕ} {D L K : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) (hK : 0 < K) :
    spectralBudgetValue n D L K = K / L *
      (budgetPhase (K * L / (4 * D * (n : ℝ) ^ 2)) ^ 2 /
        (K * L / (4 * D * (n : ℝ) ^ 2))) := by
  unfold spectralBudgetValue
  field_simp [ne_of_gt hD, ne_of_gt hL, ne_of_gt hK,
    ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

theorem spectralBudgetValue_strictMonoOn {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    StrictMonoOn (spectralBudgetValue n D L) (Ioi 0) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : 0 < 4 * D * (n : ℝ) ^ 2 := by positivity
  have hs : 0 < 4 * D * (n : ℝ) ^ 2 / L ^ 2 := div_pos hc (sq_pos_of_pos hL)
  intro K hK J hJ hKJ
  have hKa : 0 < K * L / (4 * D * (n : ℝ) ^ 2) := div_pos (mul_pos hK hL) hc
  have hJa : 0 < J * L / (4 * D * (n : ℝ) ^ 2) := div_pos (mul_pos hJ hL) hc
  have hab := budgetPhase_strictMonoOn hKa hJa
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hKJ hL) hc)
  have hz := budgetPhase_pos hKa
  unfold spectralBudgetValue
  apply mul_lt_mul_of_pos_left _ hs
  nlinarith

theorem spectralBudgetValue_strong_limit {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    Tendsto (spectralBudgetValue n D L) atTop
      (𝓝 (D * Real.pi ^ 2 * (n : ℝ) ^ 2 / L ^ 2)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : 0 < L / (4 * D * (n : ℝ) ^ 2) := by positivity
  have ha : Tendsto (fun K : ℝ => K * L / (4 * D * (n : ℝ) ^ 2)) atTop atTop := by
    simpa only [mul_div_assoc, id_eq] using tendsto_id.atTop_mul_const hc
  have ht := ((budgetPhase_tendsto_atTop.comp ha).pow 2).const_mul
    (4 * D * (n : ℝ) ^ 2 / L ^ 2)
  have hv : (4 * D * (n : ℝ) ^ 2 / L ^ 2) * (Real.pi / 2) ^ 2 =
      D * Real.pi ^ 2 * (n : ℝ) ^ 2 / L ^ 2 := by ring
  unfold spectralBudgetValue
  simpa only [Function.comp_apply, hv] using ht

theorem spectral_parameter_weak_limit {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    Tendsto (fun K : ℝ => K * L / (4 * D * (n : ℝ) ^ 2)) (𝓝[>] 0) (𝓝[>] 0) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : ContinuousAt (fun K : ℝ => K * L / (4 * D * (n : ℝ) ^ 2)) 0 := by fun_prop
    simpa using h.tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with K hK
    exact div_pos (mul_pos hK hL) (by positivity)

theorem spectralBudgetValue_weak_ratio_limit {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    Tendsto (fun K : ℝ => spectralBudgetValue n D L K / K) (𝓝[>] 0) (𝓝 (1 / L)) := by
  have ht := (budgetPhase_sq_div_tendsto_zero.comp (spectral_parameter_weak_limit hn hD hL))
    |>.const_mul (1 / L)
  apply (show Tendsto (fun K : ℝ => 1 / L *
    (budgetPhase (K * L / (4 * D * (n : ℝ) ^ 2)) ^ 2 /
      (K * L / (4 * D * (n : ℝ) ^ 2)))) (𝓝[>] 0) (𝓝 (1 / L)) by
      simpa using ht).congr'
  filter_upwards [self_mem_nhdsWithin] with K hK
  change 0 < K at hK
  rw [spectralBudgetValue_ratio hn hD hL hK]
  field_simp [ne_of_gt hK]

theorem spectral_parameter_many_traps_limit {D L K : ℝ}
    (hD : 0 < D) (hL : 0 < L) (hK : 0 < K) :
    Tendsto (fun n : ℕ => K * L / (4 * D * (n : ℝ) ^ 2)) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    have h := hp.const_div_atTop (K * L / (4 * D))
    simpa only [div_div] using h
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    exact div_pos (mul_pos hK hL) (by positivity)

theorem spectralBudgetValue_many_traps_limit {D L K : ℝ}
    (hD : 0 < D) (hL : 0 < L) (hK : 0 < K) :
    Tendsto (fun n : ℕ => spectralBudgetValue n D L K) atTop (𝓝 (K / L)) := by
  have ht := (budgetPhase_sq_div_tendsto_zero.comp
    (spectral_parameter_many_traps_limit hD hL hK)).const_mul (K / L)
  apply (show Tendsto (fun n : ℕ => K / L *
    (budgetPhase (K * L / (4 * D * (n : ℝ) ^ 2)) ^ 2 /
      (K * L / (4 * D * (n : ℝ) ^ 2)))) atTop (𝓝 (K / L)) by simpa using ht).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (spectralBudgetValue_ratio hn hD hL hK).symm

end TimeTraps.Spectral
