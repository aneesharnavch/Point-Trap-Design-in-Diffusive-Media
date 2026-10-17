module

public import TimeTraps.Interval.WeightedGridIFT

@[expose] public section

/-! Differentiating the proved local critical branch gives exactly the
manuscript's finite Dirichlet first-variation system. The correction is
uniquely determined; its endpoint extension vanishes at both endpoints. -/

namespace TimeTraps.Interval

open Set Filter TimeTraps.Analysis
open scoped ContDiff Topology

variable {n : ℕ} (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)

theorem gridIFTBranch_jacobian_derivative :
    weightedGridUniformJacobian n Ω (deriv (gridIFTBranch (n := n) h hh Ω hΩ) 0) =
      -(Ω • gridIFTForcing h) := by
  let d := deriv (gridIFTBranch (n := n) h hh Ω hΩ) 0
  let L := fderiv ℝ (gridIFTResidual h Ω) (0, gridIFTBaseline n)
  have hf := ((gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n) gridIFTBaseline_midpoints).differentiableAt
    (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hp : HasDerivAt (fun ε : ℝ => (ε, gridIFTBranch (n := n) h hh Ω hΩ ε)) (1, d) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).prodMk (gridIFTBranch_hasDerivAt (n := n) h hh Ω hΩ) using 1
  have hg := hf.comp_hasDerivAt_of_eq 0 hp (by rw [gridIFTBranch_zero])
  have hz : HasDerivAt (fun ε => gridIFTResidual h Ω (ε, gridIFTBranch (n := n) h hh Ω hΩ ε)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : Fin n → ℝ)).congr_of_eventuallyEq (gridIFTBranch_residual h hh Ω hΩ)
  have hzero : L (1, d) = 0 := hg.unique hz
  have hq := congrArg (fun M : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => M d)
    (gridIFTResidual_fderiv_grid h hh Ω)
  change L (0, d) = weightedGridUniformJacobian n Ω d at hq
  have he := L.map_add ((1 : ℝ), (0 : Fin n → ℝ)) ((0 : ℝ), d)
  simp only [Prod.mk_add_mk, add_zero, zero_add] at he
  have hε : L (1, 0) = Ω • gridIFTForcing h := gridIFTResidual_fderiv_parameter h hh Ω
  rw [hε, hq] at he
  rw [he] at hzero
  funext i
  have hi := congrFun hzero i
  change Ω * gridIFTForcing h i + weightedGridUniformJacobian n Ω d i = 0 at hi
  change weightedGridUniformJacobian n Ω d i = -(Ω * gridIFTForcing h i)
  linarith

theorem gridIFTBranch_first_variation (i : Fin n) :
    discreteSecondDifference (nodalStrength (deriv (gridIFTBranch (n := n) h hh Ω hΩ) 0)) i =
      -4 * ((n : ℝ) + 1) * gridIFTForcing h i := by
  have hi := congrFun (gridIFTBranch_jacobian_derivative (n := n) h hh Ω hΩ) i
  change (Ω / (4 * ((n : ℝ) + 1))) *
      discreteSecondDifference (nodalStrength (deriv (gridIFTBranch (n := n) h hh Ω hΩ) 0)) i =
        -(Ω * gridIFTForcing h i) at hi
  have hc : (4 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  field_simp [hc] at hi
  apply mul_left_cancel₀ (ne_of_gt hΩ)
  nlinarith

theorem gridIFTBranch_correction_unique (r : Fin n → ℝ)
    (hr : ∀ i, discreteSecondDifference (nodalStrength r) i = -4 * ((n : ℝ) + 1) * gridIFTForcing h i) :
    r = deriv (gridIFTBranch (n := n) h hh Ω hΩ) 0 := by
  obtain ⟨s, _, hs⟩ := weightedGrid_first_variation_unique (gridIFTForcing (n := n) h)
  exact (hs r hr).trans (hs _ (gridIFTBranch_first_variation h hh Ω hΩ)).symm

end TimeTraps.Interval
