module

public import TimeTraps.Interval.WeightedGridIFTTaylorDesign

@[expose] public section

/-! The affine branch's transformed trap curves. These provide a C²
comparison curve for physical inverse-coordinate perturbation estimates. -/

namespace TimeTraps.Interval

open Set
open scoped Topology ContDiff

variable {n : ℕ} (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)

noncomputable def gridIFTBranchMidpoint (i : Fin (n + 1)) (ε : ℝ) : ℝ :=
  (cdfNode (gridIFTBranch h hh Ω hΩ ε) i.castSucc +
    cdfNode (gridIFTBranch h hh Ω hΩ ε) i.succ) / 2

theorem gridIFTBranch_node_derivative (v : Fin (n + 2)) :
    HasDerivAt (fun ε => cdfNode (gridIFTBranch h hh Ω hΩ ε) v)
      (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) v) 0 := by
  refine Fin.cases ?_ (fun k => ?_) v
  · simpa only [cdfNode_first, nodalStrength_first] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change HasDerivAt (fun ε => cdfNode (gridIFTBranch h hh Ω hΩ ε) (Fin.last (n + 1)))
        (nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) (Fin.last (n + 1))) 0
      simpa only [cdfNode_last, nodalStrength_last] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · simpa only [cdfNode_site,
        show nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc.succ =
          deriv (gridIFTBranch h hh Ω hΩ) 0 i from nodalStrength_trap _ i]
        using hasDerivAt_pi.mp (gridIFTBranch_hasDerivAt (n := n) h hh Ω hΩ) i

theorem gridIFTBranchMidpoint_contDiffAt (i : Fin (n + 1)) :
    ContDiffAt ℝ 2 (gridIFTBranchMidpoint h hh Ω hΩ i) 0 := by
  exact (((gridIFTNode_contDiff i.castSucc).contDiffAt.comp 0
    (gridIFTBranch_contDiffAt h hh Ω hΩ)).add
    ((gridIFTNode_contDiff i.succ).contDiffAt.comp 0
      (gridIFTBranch_contDiffAt h hh Ω hΩ))).div_const 2

theorem gridIFTBranchMidpoint_zero (i : Fin (n + 1)) :
    gridIFTBranchMidpoint h hh Ω hΩ i 0 = (2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1)) := by
  unfold gridIFTBranchMidpoint
  rw [gridIFTBranch_zero, gridIFTBaseline_nodes]
  simp only [StrictPartition.uniform, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_succ]
  field_simp
  ring

theorem gridIFTBranchMidpoint_derivative (i : Fin (n + 1)) :
    HasDerivAt (gridIFTBranchMidpoint h hh Ω hΩ i)
      ((nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc +
        nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) / 2) 0 :=
  ((gridIFTBranch_node_derivative h hh Ω hΩ i.castSucc).add
    (gridIFTBranch_node_derivative h hh Ω hΩ i.succ)).div_const 2

theorem gridIFTBranchMidpoint_zero_interior (i : Fin (n + 1)) :
    gridIFTBranchMidpoint h hh Ω hΩ i 0 ∈ Ioo (0 : ℝ) 1 := by
  rw [gridIFTBranchMidpoint_zero]
  have hi : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  constructor
  · positivity
  · apply (div_lt_one (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
    linarith

end TimeTraps.Interval
