module

public import TimeTraps.Interval.SourceDensityPerturbationDesign
public import TimeTraps.Interval.SourceInversePerturbationStability
public import TimeTraps.Interval.WeightedGridIFTBranchSites

@[expose] public section

/-! The full physical trap-position correction for actual nonlinear
stationary perturbations. The transformed optimizer is compared with the
affine branch to second order; inverse-coordinate stability transfers that
comparison to physical positions. No smooth optimizer selection is assumed. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter Asymptotics
open scoped Topology

noncomputable def StationaryPerturbation.baselineSite (S : StationaryPerturbation) {n : ℕ}
    (i : Fin (n + 1)) : ℝ :=
  (S.medium 0).source.inverse ((2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1)))

noncomputable def StationaryPerturbation.physicalCorrection (S : StationaryPerturbation) {n : ℕ}
    (i : Fin (n + 1)) : ℝ :=
  (((S.correction n i.castSucc + S.correction n i.succ) / 2 -
    ∫ t in (0 : ℝ)..S.baselineSite i, S.densityVariation t) /
    (S.medium 0).source.density (S.baselineSite i))

variable {n : ℕ} (S : StationaryPerturbation) {K : ℝ} (hK : 0 < K)

include hK

theorem StationaryPerturbation.optimal_physical_site_expansion
    (E : ∀ ε, IntervalDesign (S.medium ε) (n + 1) K)
    (hE : ∀ᶠ ε in 𝓝 (0 : ℝ), (E ε).SourceMeanOptimal) (i : Fin (n + 1)) :
    (fun ε => (E ε).geometry.site i - S.baselineSite i - ε * S.physicalCorrection i)
      =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
  let q : ℝ → ℝ := fun ε => (E ε).partition.closed.canonicalMidpoint i
  let r : ℝ → ℝ := S.affineMidpoint i
  have hq : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun ε => (E ε).partition.closed.canonicalMidpoint_mem i)
  have hr := gridIFTBranchMidpoint_contDiffAt S.profile S.profile_contDiff S.scale S.scale_pos i
  have hr₀ := gridIFTBranchMidpoint_zero_interior S.profile S.profile_contDiff S.scale S.scale_pos i
  have hβ : ContinuousOn S.densityVariation (Icc (0 : ℝ) 1) :=
    S.baseline_density_smooth.continuousOn.mul S.density_variation_smooth.continuousOn
  obtain ⟨C, _, hcomp⟩ := S.optimal_midpoints_compare (n := n) hK
  have hqr : (fun ε => q ε - r ε) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards [hcomp, hE] with ε hε hEε
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hε (E ε) hEε i
  have hcore := source_density_compared_physical_site_remainder
    (fun ε => (S.medium ε).source) S.unit_interval S.normalized S.baseline_density_smooth
    hβ S.density_expansion hq hr hr₀ hqr
  have hrzero : r 0 = (2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1)) :=
    gridIFTBranchMidpoint_zero S.profile S.profile_contDiff S.scale S.scale_pos i
  have hrderiv : deriv r 0 = (S.correction n i.castSucc + S.correction n i.succ) / 2 :=
    (gridIFTBranchMidpoint_derivative S.profile S.profile_contDiff S.scale S.scale_pos i).deriv
  apply hcore.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hE] with ε hEε
  have hsite := ((source_mean_optimal_iff hK (E ε)).mp hEε).2.1 i
  have hm : weightedCDFMidpoint (E ε).partition.width i = q ε :=
    congrFun (E ε).partition.closed.canonicalMidpoint_eq.symm i
  rw [hsite, hm]
  change (S.medium ε).source.inverse (q ε) - (S.medium 0).source.inverse (r 0) -
    ε * ((deriv r 0 - ∫ t in (0 : ℝ)..(S.medium 0).source.inverse (r 0), S.densityVariation t) /
      (S.medium 0).source.density ((S.medium 0).source.inverse (r 0))) = _
  rw [hrzero, hrderiv]
  rfl

theorem StationaryPerturbation.optimal_physical_site_derivative
    (E : ∀ ε, IntervalDesign (S.medium ε) (n + 1) K)
    (hE : ∀ᶠ ε in 𝓝 (0 : ℝ), (E ε).SourceMeanOptimal) (i : Fin (n + 1)) :
    HasDerivAt (fun ε => (E ε).geometry.site i) (S.physicalCorrection i) 0 := by
  have hrem := S.optimal_physical_site_expansion hK E hE i
  obtain ⟨C, hC⟩ := hrem.bound
  have hzero : (E 0).geometry.site i = S.baselineSite i := by
    have he : |(E 0).geometry.site i - S.baselineSite i| ≤ 0 := by
      simpa only [Real.norm_eq_abs, zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0),
        abs_zero, mul_zero] using hC.self_of_nhds
    have hh := abs_le.mp he
    linarith
  apply HasDerivAt.of_isLittleO
  simpa only [hzero, sub_zero, smul_eq_mul] using hrem.trans_isLittleO
    (isLittleO_pow_id (𝕜 := ℝ) (by decide : 1 < 2))

end TimeTraps.Interval
