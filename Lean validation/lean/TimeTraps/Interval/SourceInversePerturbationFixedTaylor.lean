module

public import TimeTraps.Interval.SourceInversePerturbationFixed
public import TimeTraps.Interval.SourceInversePerturbationRegularity
public import TimeTraps.Interval.WeightedGridIFTBranchSites

@[expose] public section

/-! The two distinct fixed-density physical-position claims. A C1
density gives a quadratic remainder along the affine optimizing branch;
a merely positive continuous density gives the same coefficient with a
little-o remainder. -/

namespace TimeTraps.Interval

open Set Filter Asymptotics TimeTraps.Analysis
open scoped Topology ContDiff

variable {n : ℕ} (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)

theorem source_fixed_density_affine_quadratic (P : SourceInterval) (hmass : P.mass = 1)
    (hρ : ContDiffOn ℝ 1 P.density (Icc P.left P.right)) (i : Fin (n + 1)) :
    (fun ε => P.inverse (gridIFTBranchMidpoint h hh Ω hΩ i ε) -
      P.inverse ((2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))) -
      ε * (((nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc +
        nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) / 2) /
        P.density (P.inverse ((2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))))))
      =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
  have hq := gridIFTBranchMidpoint_contDiffAt h hh Ω hΩ i
  have hq₀ := gridIFTBranchMidpoint_zero_interior h hh Ω hΩ i
  have hi := (source_inverse_contDiff_two P hρ).contDiffAt (Ioo_mem_nhds hq₀.1 hq₀.2)
  have hcomp := hi.comp 0 hq
  have hd := source_fixed_density_physical_derivative P hmass
    (gridIFTBranchMidpoint_derivative h hh Ω hΩ i) hq₀
  obtain ⟨C, δ, _, hδ, hb⟩ := gridIFT_quadratic_remainder
    (fun ε => P.inverse (gridIFTBranchMidpoint h hh Ω hΩ i ε)) hcomp
  apply IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hε
  have he : |ε| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  have hbε := hb ε he
  rw [hd.deriv, gridIFTBranchMidpoint_zero] at hbε
  simpa only [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hbε

theorem source_fixed_density_affine_littleO (P : SourceInterval) (hmass : P.mass = 1)
    (i : Fin (n + 1)) :
    (fun ε => P.inverse (gridIFTBranchMidpoint h hh Ω hΩ i ε) -
      P.inverse ((2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))) -
      ε * (((nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.castSucc +
        nodalStrength (deriv (gridIFTBranch h hh Ω hΩ) 0) i.succ) / 2) /
        P.density (P.inverse ((2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))))))
      =o[𝓝 (0 : ℝ)] (fun ε => ε) := by
  have hd := source_fixed_density_physical_littleO P hmass
    (gridIFTBranchMidpoint_derivative h hh Ω hΩ i)
    (gridIFTBranchMidpoint_zero_interior h hh Ω hΩ i)
  simpa only [gridIFTBranchMidpoint_zero] using hd

end TimeTraps.Interval
