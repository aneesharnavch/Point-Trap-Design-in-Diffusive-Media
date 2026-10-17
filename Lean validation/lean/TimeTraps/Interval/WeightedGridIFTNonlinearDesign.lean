module

public import TimeTraps.Interval.WeightedGridIFTNonlinear
public import TimeTraps.Interval.WeightedGridIFTNonlinearValue

@[expose] public section

/-! Midpoint and strength expansions for all actual nonlinear minimizers.
The estimates are uniform over minimizing grids and require no smooth
choice of a minimizing grid as the parameter varies. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

variable {n : ℕ} (W : ℝ → CellWeight) (h : ℝ → ℝ)
  (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)
  (hexp : SourceUniformExpansion (fun ε => (W ε).value) (fun _ => Ω) (fun z => Ω * h z))

include hexp

theorem gridIFT_nonlinear_midpoints_compare :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost (W ε) ≤ P.gridCost (W ε)) →
      ∀ i : Fin (n + 1), |Q.canonicalMidpoint i -
        (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc +
          cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) / 2| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gridIFT_nonlinear_nodes_compare (n := n) W h hh Ω hΩ hexp
  refine ⟨C, hC, hb.mono ?_⟩
  intro ε hε Q hQ i
  have hl := hε Q hQ i.castSucc
  have hr := hε Q hQ i.succ
  have he : Q.canonicalMidpoint i -
      (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc +
        cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) / 2 =
      ((Q.point i.castSucc - cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc) +
        (Q.point i.succ - cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ)) / 2 := by
    unfold ClosedPartition.canonicalMidpoint
    ring
  rw [he, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  apply (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
  exact (abs_add_le _ _).trans (by linarith)

theorem gridIFT_nonlinear_widths_compare :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost (W ε) ≤ P.gridCost (W ε)) →
      ∀ i : Fin (n + 1), |Q.width i -
        (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
          cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc)| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gridIFT_nonlinear_nodes_compare (n := n) W h hh Ω hΩ hexp
  refine ⟨2 * C, by positivity, hb.mono ?_⟩
  intro ε hε Q hQ i
  have hl := hε Q hQ i.castSucc
  have hr := hε Q hQ i.succ
  have he : Q.width i -
      (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
        cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc) =
      (Q.point i.succ - cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) -
        (Q.point i.castSucc - cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc) := by
    unfold ClosedPartition.width
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

theorem gridIFT_nonlinear_midpoint_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost (W ε) ≤ P.gridCost (W ε)) →
      ∀ i : Fin (n + 1), |Q.canonicalMidpoint i -
        (2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1)) -
        ε * (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc +
          nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) / 2| ≤ C * ε ^ 2 := by
  obtain ⟨B, hB, hcomp⟩ := gridIFT_nonlinear_midpoints_compare (n := n) W h hh Ω hΩ hexp
  obtain ⟨C, δ, hC, hδ, haff⟩ := gridIFTBranch_midpoint_expansion (n := n) h hh Ω hΩ
  have hs : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < δ := by
    have ht : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds 0 hδ
    exact ht.mono (fun _ he => by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he)
  refine ⟨B + C, by positivity, ?_⟩
  filter_upwards [hcomp, hs] with ε hε hsε
  intro Q hQ i
  have hc := hε Q hQ i
  have ha := haff ε hsε i
  let m := (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc +
    cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) / 2
  let b := (2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))
  let r := (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc +
    nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) / 2
  change |Q.canonicalMidpoint i - m| ≤ B * ε ^ 2 at hc
  have ha' : |m - b - ε * r| ≤ C * ε ^ 2 := by
    convert! ha using 1
    congr 1
    dsimp only [m, b, r]
    ring
  have hsum := (abs_add_le (Q.canonicalMidpoint i - m) (m - b - ε * r)).trans (add_le_add hc ha')
  have he : Q.canonicalMidpoint i - m + (m - b - ε * r) = Q.canonicalMidpoint i - b - ε * r := by ring
  rw [he] at hsum
  convert! hsum using 1
  · congr 1
    dsimp only [b, r]
    ring
  · ring

theorem gridIFT_nonlinear_strength_expansion (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost (W ε) ≤ P.gridCost (W ε)) →
      ∀ i : Fin (n + 1), |K * Q.width i - K / ((n : ℝ) + 1) -
        ε * K * (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ -
          nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc)| ≤ C * ε ^ 2 := by
  obtain ⟨B, hB, hcomp⟩ := gridIFT_nonlinear_widths_compare (n := n) W h hh Ω hΩ hexp
  obtain ⟨C, δ, hC, hδ, haff⟩ := gridIFTBranch_strength_expansion (n := n) h hh Ω hΩ K
  have hs : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < δ := by
    have ht : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds 0 hδ
    exact ht.mono (fun _ he => by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he)
  refine ⟨|K| * B + C, by positivity, ?_⟩
  filter_upwards [hcomp, hs] with ε hε hsε
  intro Q hQ i
  have hc := hε Q hQ i
  have ha := haff ε hsε i
  let d := cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
    cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc
  let b := K / ((n : ℝ) + 1)
  let r := K * (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ -
    nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc)
  have hc' : |K * (Q.width i - d)| ≤ |K| * B * ε ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg K)).trans_eq (by ring)
  have ha' : |K * d - b - ε * r| ≤ C * ε ^ 2 := by
    convert! ha using 1
    congr 1
    dsimp only [d, b, r]
    ring
  have hsum := (abs_add_le (K * (Q.width i - d)) (K * d - b - ε * r)).trans (add_le_add hc' ha')
  have he : K * (Q.width i - d) + (K * d - b - ε * r) = K * Q.width i - b - ε * r := by ring
  rw [he] at hsum
  convert! hsum using 1
  · congr 1
    dsimp only [b, r]
    ring
  · ring

end TimeTraps.Interval
