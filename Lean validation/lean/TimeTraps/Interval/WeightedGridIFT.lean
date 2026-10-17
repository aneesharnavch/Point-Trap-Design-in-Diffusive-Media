module

public import TimeTraps.Interval.WeightedGridIFTDerivative

@[expose] public section

/-! The local C² branch of critical weighted grids. All implicit-function
hypotheses are proved for the actual parameterized centroid residual.
Global-minimizer concentration and quantitative Taylor remainders are
separate statements. -/

namespace TimeTraps.Interval

open Set Filter
open scoped ContDiff Topology

variable {n : ℕ} (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)

noncomputable def gridIFTBranch : ℝ → (Fin n → ℝ) :=
  (gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).implicitFunction
    (by norm_num) (gridIFTResidual_grid_invertible h hh Ω hΩ)

theorem gridIFTBranch_zero : gridIFTBranch (n := n) h hh Ω hΩ 0 = gridIFTBaseline n :=
  (gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).implicitFunction_apply_self
    (by norm_num) (gridIFTResidual_grid_invertible h hh Ω hΩ)

theorem gridIFTBranch_contDiffAt : ContDiffAt ℝ 2 (gridIFTBranch (n := n) h hh Ω hΩ) 0 :=
  (gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).contDiffAt_implicitFunction
    (by norm_num) (gridIFTResidual_grid_invertible h hh Ω hΩ)

theorem gridIFTBranch_residual :
    ∀ᶠ ε in 𝓝 (0 : ℝ), gridIFTResidual h Ω (ε, gridIFTBranch (n := n) h hh Ω hΩ ε) = 0 := by
  have he := (gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).eventually_apply_implicitFunction
    (by norm_num) (gridIFTResidual_grid_invertible h hh Ω hΩ)
  simpa only [gridIFTBranch, gridIFTResidual_baseline] using he

theorem gridIFTBranch_local_unique :
    ∀ᶠ v in 𝓝 ((0 : ℝ), gridIFTBaseline n),
      gridIFTResidual h Ω v = 0 ↔ gridIFTBranch h hh Ω hΩ v.1 = v.2 := by
  have he := (gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).eventually_apply_eq_iff_implicitFunction
    (by norm_num) (gridIFTResidual_grid_invertible h hh Ω hΩ)
  simpa only [gridIFTBranch, gridIFTResidual_baseline] using he

theorem gridIFTBranch_hasDerivAt :
    HasDerivAt (gridIFTBranch (n := n) h hh Ω hΩ) (deriv (gridIFTBranch h hh Ω hΩ) 0) 0 :=
  ((gridIFTBranch_contDiffAt (n := n) h hh Ω hΩ).differentiableAt (by norm_num)).hasDerivAt

end TimeTraps.Interval
