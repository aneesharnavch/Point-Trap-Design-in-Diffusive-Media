module

public import TimeTraps.Interval.SourceInversePerturbationRegularity
public import TimeTraps.Interval.WeightedGridIFTTaylor

@[expose] public section

/-! The physical-site quadratic remainder. A C2 transformed site curve
is composed with the actual varying inverse coordinate. The coefficient
expansion and the derived inverse expansion supply uniform control; the
baseline inverse and its variation coefficient supply the required spatial
regularity. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter Asymptotics TimeTraps.Analysis
open scoped Topology ContDiff

theorem source_uniform_expansion_moving_remainder {f : ℝ → ℝ → ℝ} {f₀ f₁ q : ℝ → ℝ}
    (hf : SourceUniformExpansion f f₀ f₁)
    (hqrange : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Icc (0 : ℝ) 1)
    (hbase : ContDiffAt ℝ 2 (fun ε => f₀ (q ε)) 0)
    (hfirst : DifferentiableAt ℝ (fun ε => f₁ (q ε)) 0) :
    (fun ε => f ε (q ε) - f₀ (q 0) -
      ε * (deriv (fun e => f₀ (q e)) 0 + f₁ (q 0))) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
  obtain ⟨C, _, hC⟩ := hf
  have hr : (fun ε : ℝ => f ε (q ε) - f₀ (q ε) - ε * f₁ (q ε)) =O[𝓝 0] (fun ε => ε ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards [hC, hqrange] with ε hε hqe
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hε (q ε) hqe
  obtain ⟨B, δ, _, hδ, hb⟩ := gridIFT_quadratic_remainder (fun ε => f₀ (q ε)) hbase
  have hbaseO : (fun ε => f₀ (q ε) - f₀ (q 0) - ε * deriv (fun e => f₀ (q e)) 0)
      =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
    apply IsBigO.of_bound B
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hε
    have he : |ε| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
    simpa only [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hb ε he
  have hfirstO : (fun ε => (f₁ (q ε) - f₁ (q 0)) * ε) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
    simpa only [sub_zero, ← sq] using hfirst.isBigO_sub.mul
      (isBigO_refl (fun ε : ℝ => ε) (𝓝 0))
  exact ((hr.add hbaseO).add hfirstO).congr_left (fun ε => by ring)

theorem source_density_physical_site_remainder (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    (hreg : ContDiffOn ℝ 1 (P 0).density (Icc (0 : ℝ) 1))
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β)
    {q : ℝ → ℝ} (hq : ContDiffAt ℝ 2 q 0) (hq₀ : q 0 ∈ Ioo (0 : ℝ) 1) :
    (fun ε => (P ε).inverse (q ε) - (P 0).inverse (q 0) -
      ε * ((deriv q 0 - ∫ t in (0 : ℝ)..(P 0).inverse (q 0), β t) /
        (P 0).density ((P 0).inverse (q 0)))) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
  have hqin : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Ioo (0 : ℝ) 1 :=
    hq.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hq₀)
  have hqrange := hqin.mono (fun _ h => Ioo_subset_Icc_self h)
  have hreg' : ContDiffOn ℝ 1 (P 0).density (Icc (P 0).left (P 0).right) := by
    simpa only [(hshape 0).1, (hshape 0).2] using hreg
  have hi := (source_inverse_contDiff_two (P 0) hreg').contDiffAt
    (Ioo_mem_nhds hq₀.1 hq₀.2)
  have hvar := (source_inverse_variation_contDiff_one (P 0) (hshape 0).1 (hshape 0).2 hreg hβ).contDiffAt
    (Ioo_mem_nhds hq₀.1 hq₀.2)
  have he := source_uniform_expansion_moving_remainder
    (source_density_inverse_expansion P hshape hmass hreg hβ hρ) hqrange
    (hi.comp 0 hq) ((hvar.comp 0 (hq.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))).differentiableAt (by norm_num))
  have hd := ((P 0).inverse_derivative hq₀).comp 0
    (hq.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasDerivAt
  have hd' : deriv (fun e => (P 0).inverse (q e)) 0 =
      (1 / (P 0).density ((P 0).inverse (q 0))) * deriv q 0 := by
    simpa only [hmass.self_of_nhds, Function.comp_def] using hd.deriv
  apply he.congr_left
  intro ε
  rw [hd']
  ring

end TimeTraps.Interval
