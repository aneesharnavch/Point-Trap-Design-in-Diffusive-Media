module

public import TimeTraps.Interval.SourceDensityPerturbationModel
public import TimeTraps.Interval.SourceMeanPullbackOptimality
public import TimeTraps.Interval.WeightedGridIFTNonlinearDesign

@[expose] public section

/-! Uniform perturbation formulas for every actual physical mean
optimizer. N=n+1 is the positive number of interior traps; the correction
has n free cumulative-grid coordinates and zero endpoint values. No
regularity is assumed of a choice of physical optimizing designs. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology

variable {n : ℕ} (S : StationaryPerturbation) {K : ℝ} (hK : 0 < K)

include hK

theorem StationaryPerturbation.optimal_midpoints_compare :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ E : IntervalDesign (S.medium ε) (n + 1) K, E.SourceMeanOptimal →
      ∀ i : Fin (n + 1), |E.partition.closed.canonicalMidpoint i - S.affineMidpoint i ε| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gridIFT_nonlinear_midpoints_compare (n := n)
    (fun ε => (S.medium ε).cellWeight) S.profile S.profile_contDiff S.scale S.scale_pos S.effective_expansion
  refine ⟨C, hC, hb.mono ?_⟩
  intro ε hε E hE i
  exact hε E.partition.closed ((source_mean_optimal_iff hK E).mp hE).2.2 i

theorem StationaryPerturbation.optimal_strength_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ E : IntervalDesign (S.medium ε) (n + 1) K, E.SourceMeanOptimal →
      ∀ i : Fin (n + 1), |E.strength i - K / ((n : ℝ) + 1) -
        ε * K * (S.correction n i.succ - S.correction n i.castSucc)| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gridIFT_nonlinear_strength_expansion (n := n)
    (fun ε => (S.medium ε).cellWeight) S.profile S.profile_contDiff S.scale S.scale_pos S.effective_expansion K
  refine ⟨C, hC, hb.mono ?_⟩
  intro ε hε E hE i
  obtain ⟨hκ, _, hgrid⟩ := (source_mean_optimal_iff hK E).mp hE
  rw [hκ i]
  exact hε E.partition.closed hgrid i

theorem StationaryPerturbation.optimal_source_sites_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ E : IntervalDesign (S.medium ε) (n + 1) K, E.SourceMeanOptimal →
      ∀ i : Fin (n + 1), |(S.medium ε).source.coordinate (E.geometry.site i) -
        (2 * (i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1)) -
        ε * (S.correction n i.castSucc + S.correction n i.succ) / 2| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gridIFT_nonlinear_midpoint_expansion (n := n)
    (fun ε => (S.medium ε).cellWeight) S.profile S.profile_contDiff S.scale S.scale_pos S.effective_expansion
  refine ⟨C, hC, hb.mono ?_⟩
  intro ε hε E hE i
  obtain ⟨_, hsite, hgrid⟩ := (source_mean_optimal_iff hK E).mp hE
  have hm : weightedCDFMidpoint E.partition.width i = E.partition.closed.canonicalMidpoint i := by
    exact congrFun E.partition.closed.canonicalMidpoint_eq.symm i
  rw [hsite i, hm, (S.medium ε).source.coordinate_inverse (E.partition.closed.canonicalMidpoint_mem i)]
  exact hε E.partition.closed hgrid i

theorem StationaryPerturbation.optimal_mean_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ E : IntervalDesign (S.medium ε) (n + 1) K, E.SourceMeanOptimal →
      |E.sourceMeanCost - (1 / K + S.scale / (12 * ((n : ℝ) + 1) ^ 2)) -
        ε * gridIFTValueCoefficient S.profile S.scale n| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gridIFT_nonlinear_minimum_value_expansion (n := n)
    (fun ε => (S.medium ε).cellWeight) S.profile S.profile_contDiff S.scale S.scale_pos S.effective_expansion
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, S.normalized] with ε hε hmε
  intro E hE
  have hgrid := ((source_mean_optimal_iff hK E).mp hE).2.2
  have hcost := (source_mean_optimal_iff_cost_eq hK E.partition hgrid E).mp hE
  rw [hmε] at hcost
  rw [hcost]
  have hv := hε E.partition.closed hgrid
  simpa only [add_sub_add_left_eq_sub] using hv

theorem StationaryPerturbation.optimal_mean_derivative
    (E : ∀ ε, IntervalDesign (S.medium ε) (n + 1) K)
    (hE : ∀ᶠ ε in 𝓝 (0 : ℝ), (E ε).SourceMeanOptimal) :
    HasDerivAt (fun ε => (E ε).sourceMeanCost) (gridIFTValueCoefficient S.profile S.scale n) 0 := by
  obtain ⟨C, _, hb⟩ := S.optimal_mean_expansion (n := n) hK
  have hzero : (E 0).sourceMeanCost = 1 / K + S.scale / (12 * ((n : ℝ) + 1) ^ 2) := by
    have h := hb.self_of_nhds (E 0) hE.self_of_nhds
    have he : |(E 0).sourceMeanCost - (1 / K + S.scale / (12 * ((n : ℝ) + 1) ^ 2))| ≤ 0 := by
      simpa using h
    have hh := abs_le.mp he
    linarith
  have ho : (fun ε => (E ε).sourceMeanCost - (E 0).sourceMeanCost -
      ε * gridIFTValueCoefficient S.profile S.scale n) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hb, hE] with ε hε hEε
    simpa only [hzero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hε (E ε) hEε
  apply HasDerivAt.of_isLittleO
  simpa only [sub_zero, smul_eq_mul] using ho.trans_isLittleO
    (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by decide : 1 < 2))

end TimeTraps.Interval
