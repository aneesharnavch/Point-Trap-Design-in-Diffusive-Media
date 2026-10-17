module

public import TimeTraps.Interval.SourceDensityPerturbationAlgebra

@[expose] public section

/-! Uniform reciprocal and moving-coordinate expansions about a positive
constant baseline. Small-parameter lower bounds and Lipschitz constants
are derived rather than supplied as extra source hypotheses. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

theorem source_uniform_expansion_inv_const {f : ℝ → ℝ → ℝ} {f₁ : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : SourceUniformExpansion f (fun _ => c) f₁)
    (h₁ : ContinuousOn f₁ (Icc (0 : ℝ) 1)) :
    SourceUniformExpansion (fun ε x => 1 / f ε x) (fun _ => 1 / c)
      (fun x => -f₁ x / c ^ 2) := by
  obtain ⟨A, hA, hlin⟩ := source_uniform_expansion_linear_bound hf h₁
  obtain ⟨B, hB, hb⟩ := source_compact_abs_bound h₁
  obtain ⟨C, hC, hr⟩ := hf
  let K := c * C + B * A
  have hK : 0 ≤ K := add_nonneg (mul_nonneg hc.le hC) (mul_nonneg hB hA)
  let T := 2 * K / c ^ 3
  have hT : 0 ≤ T := div_nonneg (mul_nonneg (by norm_num) hK) (pow_nonneg hc.le _)
  have hδ : 0 < c / (2 * (A + 1)) := div_pos hc (by positivity)
  refine ⟨T, hT, ?_⟩
  filter_upwards [hlin, hr, Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hlinε hrε he
  have he' : |ε| < c / (2 * (A + 1)) := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he
  have hsmall : A * |ε| ≤ c / 2 := by
    have he₂ := (lt_div_iff₀ (show 0 < 2 * (A + 1) by positivity)).mp he'
    nlinarith [abs_nonneg ε]
  intro x hx
  let t := f ε x
  have hlow : c / 2 ≤ t := by
    have hl := abs_le.mp (hlinε x hx)
    dsimp only [t]
    linarith
  have ht : 0 < t := (half_pos hc).trans_le hlow
  have heq : 1 / t - 1 / c - ε * (-f₁ x / c ^ 2) =
      (-c * (t - c - ε * f₁ x) + ε * f₁ x * (t - c)) / (t * c ^ 2) := by
    field_simp
    ring
  have hn₁ : |-c * (t - c - ε * f₁ x)| ≤ c * (C * ε ^ 2) := by
    rw [abs_mul, abs_neg, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hrε x hx) hc.le
  have hn₂ : |ε * f₁ x * (t - c)| ≤ B * A * ε ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (|ε| * B) * (A * |ε|) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg ε)) (hlinε x hx)
        (abs_nonneg _) (mul_nonneg (abs_nonneg ε) hB)
      _ = B * A * |ε| ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  have hn : |-c * (t - c - ε * f₁ x) + ε * f₁ x * (t - c)| ≤ K * ε ^ 2 := by
    have hs := (abs_add_le _ _).trans (add_le_add hn₁ hn₂)
    dsimp only [K]
    nlinarith
  change |1 / t - 1 / c - ε * (-f₁ x / c ^ 2)| ≤ T * ε ^ 2
  rw [heq, abs_div, abs_of_pos (mul_pos ht (sq_pos_of_pos hc))]
  apply (div_le_iff₀ (mul_pos ht (sq_pos_of_pos hc))).mpr
  have hTm : T * ((c / 2) * c ^ 2) = K := by
    dsimp only [T]
    field_simp
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hlow (sq_nonneg c)) (mul_nonneg hT (sq_nonneg ε))
  have hright : K * ε ^ 2 ≤ T * ε ^ 2 * (t * c ^ 2) := by
    calc
      _ = T * ε ^ 2 * ((c / 2) * c ^ 2) := by rw [← hTm]; ring
      _ ≤ _ := hm
  exact hn.trans hright

theorem source_uniform_expansion_comp_const {f q : ℝ → ℝ → ℝ} {f₁ q₁ : ℝ → ℝ} {c : ℝ}
    (hf : SourceUniformExpansion f (fun _ => c) f₁)
    (hq : SourceUniformExpansion q (q 0) q₁)
    (hq₁ : ContinuousOn q₁ (Icc (0 : ℝ) 1))
    (hf₁ : ContDiffOn ℝ 1 f₁ (Icc (0 : ℝ) 1))
    (hqr : ∀ ε y, y ∈ Icc (0 : ℝ) 1 → q ε y ∈ Icc (0 : ℝ) 1) :
    SourceUniformExpansion (fun ε y => f ε (q ε y)) (fun _ => c) (fun y => f₁ (q 0 y)) := by
  obtain ⟨A, hA, hlin⟩ := source_uniform_expansion_linear_bound hq hq₁
  obtain ⟨L, hL⟩ := hf₁.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 1) isCompact_Icc
  obtain ⟨C, hC, hr⟩ := hf
  refine ⟨C + (L : ℝ) * A, add_nonneg hC (mul_nonneg L.coe_nonneg hA), ?_⟩
  filter_upwards [hlin, hr] with ε hlinε hrε
  intro y hy
  have hLip : |f₁ (q ε y) - f₁ (q 0 y)| ≤ (L : ℝ) * |q ε y - q 0 y| := by
    simpa only [Real.dist_eq] using hL.dist_le_mul _ (hqr ε y hy) _ (hqr 0 y hy)
  have he : f ε (q ε y) - c - ε * f₁ (q 0 y) =
      (f ε (q ε y) - c - ε * f₁ (q ε y)) + ε * (f₁ (q ε y) - f₁ (q 0 y)) := by ring
  have hp : |ε * (f₁ (q ε y) - f₁ (q 0 y))| ≤ (L : ℝ) * A * ε ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ |ε| * ((L : ℝ) * (A * |ε|)) := mul_le_mul_of_nonneg_left
        (hLip.trans (mul_le_mul_of_nonneg_left (hlinε y hy) L.coe_nonneg)) (abs_nonneg ε)
      _ = (L : ℝ) * A * |ε| ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  change |f ε (q ε y) - c - ε * f₁ (q 0 y)| ≤ _
  rw [he]
  have hs := (abs_add_le _ _).trans (add_le_add (hrε _ (hqr ε y hy)) hp)
  nlinarith

end TimeTraps.Interval
