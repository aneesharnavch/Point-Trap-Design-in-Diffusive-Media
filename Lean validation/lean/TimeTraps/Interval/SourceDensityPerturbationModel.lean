module

public import TimeTraps.Interval.SourceDensityPerturbationUniform
public import TimeTraps.Interval.SourceInversePerturbationClosed
public import TimeTraps.Interval.WeightedGridIFTVariation

@[expose] public section

/-! A package of the manuscript's stationary-density perturbation
hypotheses. It contains actual media and coefficient Taylor hypotheses,
not conclusions about effective weights or optimal designs. The derived
profile and scale connect this data to the grid perturbation theorems. -/

namespace TimeTraps.Interval

open Set Filter TimeTraps.Analysis
open scoped Topology ContDiff

structure StationaryPerturbation where
  medium : ℝ → IntervalMedium
  unit_interval : ∀ ε, (medium ε).source.left = 0 ∧ (medium ε).source.right = 1
  normalized : ∀ᶠ ε in 𝓝 (0 : ℝ), (medium ε).source.mass = 1
  relativeConductance : ℝ → ℝ
  relativeDensity : ℝ → ℝ
  baseline_density_smooth : ContDiffOn ℝ 1 (medium 0).source.density (Icc (0 : ℝ) 1)
  conductance_variation_smooth : ContDiffOn ℝ 1 relativeConductance (Icc (0 : ℝ) 1)
  density_variation_smooth : ContDiffOn ℝ 1 relativeDensity (Icc (0 : ℝ) 1)
  conductance_expansion : SourceUniformExpansion (fun ε => (medium ε).conductance)
    (medium 0).conductance (fun x => (medium 0).conductance x * relativeConductance x)
  density_expansion : SourceUniformExpansion (fun ε => (medium ε).source.density)
    (medium 0).source.density (fun x => (medium 0).source.density x * relativeDensity x)
  baselineProduct : ℝ
  product_constant : ∀ x ∈ Icc (0 : ℝ) 1,
    (medium 0).conductance x * (medium 0).source.density x = baselineProduct

noncomputable def StationaryPerturbation.scale (S : StationaryPerturbation) : ℝ :=
  1 / S.baselineProduct

noncomputable def StationaryPerturbation.profile (S : StationaryPerturbation) (y : ℝ) : ℝ :=
  -(S.relativeConductance ((S.medium 0).source.inverse y) +
    S.relativeDensity ((S.medium 0).source.inverse y))

def StationaryPerturbation.densityVariation (S : StationaryPerturbation) (x : ℝ) : ℝ :=
  (S.medium 0).source.density x * S.relativeDensity x

theorem StationaryPerturbation.scale_pos (S : StationaryPerturbation) : 0 < S.scale := by
  have hzero : (0 : ℝ) ∈ Icc (S.medium 0).source.left (S.medium 0).source.right := by
    simp only [(S.unit_interval 0).1, (S.unit_interval 0).2, mem_Icc]
    exact ⟨le_rfl, zero_le_one⟩
  have hc : 0 < S.baselineProduct := by
    rw [← S.product_constant 0 ⟨le_rfl, zero_le_one⟩]
    exact mul_pos ((S.medium 0).conductance_pos 0 hzero) ((S.medium 0).source.positive 0 hzero)
  exact one_div_pos.mpr hc

theorem StationaryPerturbation.profile_contDiff (S : StationaryPerturbation) :
    ContDiffOn ℝ 1 S.profile (Icc (0 : ℝ) 1) :=
  source_density_perturbation_profile_contDiff (S.medium 0).source
    (S.unit_interval 0).1 (S.unit_interval 0).2
    S.conductance_variation_smooth S.density_variation_smooth

theorem StationaryPerturbation.effective_expansion (S : StationaryPerturbation) :
    SourceUniformExpansion (fun ε => (S.medium ε).cellWeight.value) (fun _ => S.scale)
      (fun y => S.scale * S.profile y) := by
  have h := source_density_effective_weight_expansion S.medium S.unit_interval S.normalized
    S.baseline_density_smooth S.conductance_variation_smooth S.density_variation_smooth
    S.conductance_expansion S.density_expansion S.product_constant
  have he : (fun y => S.scale * S.profile y) =
      (fun y => -(S.relativeConductance ((S.medium 0).source.inverse y) +
        S.relativeDensity ((S.medium 0).source.inverse y)) / S.baselineProduct) := by
    funext y
    dsimp only [scale, profile]
    ring
  rw [he]
  exact h

noncomputable def StationaryPerturbation.branch (S : StationaryPerturbation) (n : ℕ) : ℝ → Fin n → ℝ :=
  gridIFTBranch S.profile S.profile_contDiff S.scale S.scale_pos

noncomputable def StationaryPerturbation.correction (S : StationaryPerturbation) (n : ℕ) :
    Fin (n + 2) → ℝ := nodalStrength (deriv (S.branch n) 0)

noncomputable def StationaryPerturbation.affineMidpoint (S : StationaryPerturbation) {n : ℕ}
    (i : Fin (n + 1)) (ε : ℝ) : ℝ :=
  (cdfNode (S.branch n ε) i.castSucc + cdfNode (S.branch n ε) i.succ) / 2

end TimeTraps.Interval
