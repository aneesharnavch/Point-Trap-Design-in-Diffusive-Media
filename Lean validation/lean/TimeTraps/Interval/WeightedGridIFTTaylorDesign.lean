module

public import TimeTraps.Interval.WeightedGridIFTTaylor
public import TimeTraps.Interval.WeightedGridIFTGlobalAttainment

@[expose] public section

/-! Source-coordinate trap midpoints and budget shares along the globally
optimal branch, with uniform quadratic remainders at fixed grid size. -/

namespace TimeTraps.Interval

open Set
open scoped Topology ContDiff

variable {n : ℕ} (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)

theorem gridIFTBranch_nodes_expansion :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ v : Fin (n + 2),
      |cdfNode (gridIFTBranch h hh Ω hΩ ε) v - (v.val : ℝ) / ((n : ℝ) + 1) -
        ε * nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) v| ≤ C * ε ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := gridIFTBranch_coordinate_expansion (n := n) h hh Ω hΩ
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ε hε v
  have hp : 0 ≤ C * ε ^ 2 := mul_nonneg hC.le (sq_nonneg ε)
  refine Fin.cases ?_ (fun k => ?_) v
  · simpa only [cdfNode_first, Fin.val_zero, Nat.cast_zero, zero_div, nodalStrength_first,
      mul_zero, sub_zero, abs_zero] using hp
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change |cdfNode _ (Fin.last (n + 1)) - (((Fin.last (n + 1)).val : ℕ) : ℝ) / _ -
        ε * nodalStrength _ (Fin.last (n + 1))| ≤ _
      simpa only [cdfNode_last, Fin.val_last, Nat.cast_add, Nat.cast_one,
        div_self (show (n : ℝ) + 1 ≠ 0 by positivity), nodalStrength_last,
        mul_zero, sub_self, sub_zero, abs_zero] using hp
    · simpa only [cdfNode_site, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
        show nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc.succ =
          deriv (gridIFTBranch h hh Ω hΩ) 0 i from nodalStrength_trap _ i,
        gridIFTBaseline] using hb ε hε i

theorem gridIFTBranch_midpoint_expansion :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ i : Fin (n + 1),
      |(cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc +
          cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) / 2 -
        (2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1)) -
        ε * (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc +
          nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) / 2| ≤ C * ε ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := gridIFTBranch_nodes_expansion (n := n) h hh Ω hΩ
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ε hε i
  have hl := hb ε hε i.castSucc
  have hr := hb ε hε i.succ
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hl hr
  have he : (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc +
        cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) / 2 -
      (2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1)) -
      ε * (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc +
        nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) / 2 =
      ((cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc -
          (i.val : ℝ) / ((n : ℝ) + 1) -
          ε * nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc) +
        (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
          ((i.val : ℝ) + 1) / ((n : ℝ) + 1) -
          ε * nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ)) / 2 := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  apply (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
  exact (abs_add_le _ _).trans (by linarith)

theorem gridIFTBranch_strength_expansion (K : ℝ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ i : Fin (n + 1),
      |K * (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
          cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc) - K / ((n : ℝ) + 1) -
        ε * K * (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ -
          nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc)| ≤ C * ε ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := gridIFTBranch_nodes_expansion (n := n) h hh Ω hΩ
  refine ⟨2 * |K| * C + 1, δ, by positivity, hδ, ?_⟩
  intro ε hε i
  have hl := hb ε hε i.castSucc
  have hr := hb ε hε i.succ
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hl hr
  have he : K * (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
        cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc) - K / ((n : ℝ) + 1) -
      ε * K * (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ -
        nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc) =
      K * ((cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
          ((i.val : ℝ) + 1) / ((n : ℝ) + 1) -
          ε * nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) -
        (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc -
          (i.val : ℝ) / ((n : ℝ) + 1) -
          ε * nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc)) := by
    ring
  rw [he, abs_mul]
  calc
    _ ≤ |K| * (2 * C * ε ^ 2) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith)) (abs_nonneg K)
    _ ≤ (2 * |K| * C + 1) * ε ^ 2 := by nlinarith [sq_nonneg ε]

theorem ClosedPartition.gridIFTBranch_design (Q : ClosedPartition (n + 1)) (ε : ℝ)
    (hQ : Q.point = cdfNode (gridIFTBranch h hh Ω hΩ ε)) (i : Fin (n + 1)) :
    Q.canonicalMidpoint i = (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc +
        cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) / 2 ∧
    Q.width i = cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ -
        cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc := by
  simp only [ClosedPartition.canonicalMidpoint, ClosedPartition.width, hQ, and_self]

end TimeTraps.Interval
