module

public import TimeTraps.Interval.SourceDensityPerturbation

@[expose] public section

/-! Algebra of uniform coefficient expansions on the compact unit
interval. Boundedness constants are derived from continuity. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology

theorem source_compact_abs_bound {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ B := by
  obtain ⟨x, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hf.abs
  exact ⟨|f x|, abs_nonneg _, fun _ hy => hmax hy⟩

theorem source_uniform_expansion_linear_bound {f : ℝ → ℝ → ℝ} {f₀ f₁ : ℝ → ℝ}
    (hf : SourceUniformExpansion f f₀ f₁) (h₁ : ContinuousOn f₁ (Icc (0 : ℝ) 1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ Icc (0 : ℝ) 1,
      |f ε x - f₀ x| ≤ A * |ε| := by
  obtain ⟨B, hB, hb⟩ := source_compact_abs_bound h₁
  obtain ⟨C, hC, hr⟩ := hf
  refine ⟨B + C, add_nonneg hB hC, ?_⟩
  filter_upwards [hr, Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with ε hε he
  have he' : |ε| ≤ 1 := (show |ε| < 1 by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he).le
  have he₂ : ε ^ 2 ≤ |ε| := by nlinarith [sq_abs ε, abs_nonneg ε]
  intro x hx
  have hp : |ε * f₁ x| ≤ |ε| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg ε)
  have hs : |f ε x - f₀ x| ≤ C * ε ^ 2 + |ε| * B := by
    calc
      _ = |(f ε x - f₀ x - ε * f₁ x) + ε * f₁ x| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hε x hx) hp)
  nlinarith [mul_le_mul_of_nonneg_left he₂ hC]

theorem source_uniform_expansion_bounded {f : ℝ → ℝ → ℝ} {f₀ f₁ : ℝ → ℝ}
    (hf : SourceUniformExpansion f f₀ f₁) (h₀ : ContinuousOn f₀ (Icc (0 : ℝ) 1))
    (h₁ : ContinuousOn f₁ (Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ Icc (0 : ℝ) 1, |f ε x| ≤ M := by
  obtain ⟨B, hB, hb⟩ := source_compact_abs_bound h₀
  obtain ⟨A, hA, ha⟩ := source_uniform_expansion_linear_bound hf h₁
  refine ⟨B + A, add_nonneg hB hA, ?_⟩
  filter_upwards [ha, Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with ε hε he
  have he' : |ε| ≤ 1 := (show |ε| < 1 by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he).le
  intro x hx
  have hs : |f ε x| ≤ A * |ε| + B := by
    calc
      _ = |(f ε x - f₀ x) + f₀ x| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hε x hx) (hb x hx))
  nlinarith [mul_le_mul_of_nonneg_left he' hA]

theorem source_uniform_expansion_mul {f g : ℝ → ℝ → ℝ} {f₀ f₁ g₀ g₁ : ℝ → ℝ}
    (hf : SourceUniformExpansion f f₀ f₁) (hg : SourceUniformExpansion g g₀ g₁)
    (hf₀ : ContinuousOn f₀ (Icc (0 : ℝ) 1)) (hf₁ : ContinuousOn f₁ (Icc (0 : ℝ) 1))
    (hg₀ : ContinuousOn g₀ (Icc (0 : ℝ) 1)) (hg₁ : ContinuousOn g₁ (Icc (0 : ℝ) 1)) :
    SourceUniformExpansion (fun ε x => f ε x * g ε x) (fun x => f₀ x * g₀ x)
      (fun x => f₁ x * g₀ x + f₀ x * g₁ x) := by
  obtain ⟨M, hM, hfb⟩ := source_uniform_expansion_bounded hf hf₀ hf₁
  obtain ⟨A, hA, hfa⟩ := source_uniform_expansion_linear_bound hf hf₁
  obtain ⟨B₀, hB₀, hb₀⟩ := source_compact_abs_bound hg₀
  obtain ⟨B₁, hB₁, hb₁⟩ := source_compact_abs_bound hg₁
  obtain ⟨C, hC, hfr⟩ := hf
  obtain ⟨D, hD, hgr⟩ := hg
  refine ⟨M * D + B₀ * C + B₁ * A,
    add_nonneg (add_nonneg (mul_nonneg hM hD) (mul_nonneg hB₀ hC)) (mul_nonneg hB₁ hA), ?_⟩
  filter_upwards [hfb, hfa, hfr, hgr] with ε hfbε hfaε hfrε hgrε
  intro x hx
  have he : f ε x * g ε x - f₀ x * g₀ x - ε * (f₁ x * g₀ x + f₀ x * g₁ x) =
      f ε x * (g ε x - g₀ x - ε * g₁ x) + g₀ x * (f ε x - f₀ x - ε * f₁ x) +
      ε * g₁ x * (f ε x - f₀ x) := by ring
  have h₁ : |f ε x * (g ε x - g₀ x - ε * g₁ x)| ≤ M * (D * ε ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul (hfbε x hx) (hgrε x hx) (abs_nonneg _) hM
  have h₂ : |g₀ x * (f ε x - f₀ x - ε * f₁ x)| ≤ B₀ * (C * ε ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul (hb₀ x hx) (hfrε x hx) (abs_nonneg _) hB₀
  have h₃ : |ε * g₁ x * (f ε x - f₀ x)| ≤ B₁ * A * ε ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (|ε| * B₁) * (A * |ε|) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hb₁ x hx) (abs_nonneg ε)) (hfaε x hx)
        (abs_nonneg _) (mul_nonneg (abs_nonneg ε) hB₁)
      _ = B₁ * A * |ε| ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  change |f ε x * g ε x - f₀ x * g₀ x - ε * (f₁ x * g₀ x + f₀ x * g₁ x)| ≤ _
  rw [he]
  have hs := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃)
  nlinarith

end TimeTraps.Interval
