module

public import TimeTraps.Interval.SourceDensityPerturbationAlgebra
public import TimeTraps.Interval.SourceInversePerturbationTaylor

@[expose] public section

/-! Uniform control of the actual inverse family and physical-site
transfer from a quadratic comparison of transformed sites. No parameter
smoothness of the compared site curve is assumed. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter Asymptotics TimeTraps.Analysis
open scoped Topology ContDiff

theorem source_density_inverse_lipschitz (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ y ∈ Icc (0 : ℝ) 1,
      ∀ z ∈ Icc (0 : ℝ) 1, |(P ε).inverse y - (P ε).inverse z| ≤ M * |y - z| := by
  have hc : ContinuousOn (P 0).density (Icc (0 : ℝ) 1) := by
    simpa only [(hshape 0).1, (hshape 0).2] using (P 0).continuous
  obtain ⟨b, hb, hbmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hc
  let m := (P 0).density b
  have hm : 0 < m := (P 0).positive b (by simpa only [(hshape 0).1, (hshape 0).2] using hb)
  have hmin : ∀ x ∈ Icc (0 : ℝ) 1, m ≤ (P 0).density x := fun _ hx => hbmin hx
  obtain ⟨A, hA, hlin⟩ := source_uniform_expansion_linear_bound hρ hβ
  have hδ : 0 < m / (2 * (A + 1)) := div_pos hm (by positivity)
  refine ⟨2 / m, div_pos (by norm_num) hm, ?_⟩
  filter_upwards [hmass, hlin, Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hmε hlinε he
  have he' : |ε| < m / (2 * (A + 1)) := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he
  have hsmall : A * |ε| ≤ m / 2 := by
    have he₂ := (lt_div_iff₀ (show 0 < 2 * (A + 1) by positivity)).mp he'
    nlinarith [abs_nonneg ε]
  have hρmin : ∀ x ∈ Icc (0 : ℝ) 1, m / 2 ≤ (P ε).density x := by
    intro x hx
    have hl := abs_le.mp (hlinε x hx)
    linarith [hmin x hx]
  intro y hy z hz
  have hxy : (P ε).inverse y ∈ Icc (0 : ℝ) 1 := by
    simpa only [(hshape ε).1, (hshape ε).2] using (P ε).inverse_mem y
  have hxz : (P ε).inverse z ∈ Icc (0 : ℝ) 1 := by
    simpa only [(hshape ε).1, (hshape ε).2] using (P ε).inverse_mem z
  have hlower := source_coordinate_lower_bound (P ε) (hshape ε).1 (hshape ε).2 hmε hρmin hxy hxz
  rw [(P ε).coordinate_inverse hy, (P ε).coordinate_inverse hz] at hlower
  calc
    _ ≤ (2 * |y - z|) / m := (le_div_iff₀ hm).mpr (by nlinarith)
    _ = (2 / m) * |y - z| := by ring

theorem source_density_inverse_bigO_transfer (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β)
    {q r : ℝ → ℝ} (hq : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Icc (0 : ℝ) 1)
    (hr : ∀ᶠ ε in 𝓝 (0 : ℝ), r ε ∈ Icc (0 : ℝ) 1)
    (hqr : (fun ε => q ε - r ε) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2)) :
    (fun ε => (P ε).inverse (q ε) - (P ε).inverse (r ε)) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
  obtain ⟨M, _, hM⟩ := source_density_inverse_lipschitz P hshape hmass hβ hρ
  have hcomp : (fun ε => (P ε).inverse (q ε) - (P ε).inverse (r ε))
      =O[𝓝 (0 : ℝ)] (fun ε => q ε - r ε) := by
    apply IsBigO.of_bound M
    filter_upwards [hM, hq, hr] with ε hε hqe hre
    simpa only [Real.norm_eq_abs] using hε _ hqe _ hre
  exact hcomp.trans hqr

theorem source_density_compared_physical_site_remainder (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    (hreg : ContDiffOn ℝ 1 (P 0).density (Icc (0 : ℝ) 1))
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β)
    {q r : ℝ → ℝ} (hq : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Icc (0 : ℝ) 1)
    (hr : ContDiffAt ℝ 2 r 0) (hr₀ : r 0 ∈ Ioo (0 : ℝ) 1)
    (hqr : (fun ε => q ε - r ε) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2)) :
    (fun ε => (P ε).inverse (q ε) - (P 0).inverse (r 0) -
      ε * ((deriv r 0 - ∫ t in (0 : ℝ)..(P 0).inverse (r 0), β t) /
        (P 0).density ((P 0).inverse (r 0)))) =O[𝓝 (0 : ℝ)] (fun ε => ε ^ 2) := by
  have hri : ∀ᶠ ε in 𝓝 (0 : ℝ), r ε ∈ Ioo (0 : ℝ) 1 :=
    hr.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hr₀)
  have hrr := hri.mono (fun _ h => Ioo_subset_Icc_self h)
  have hdiff := source_density_inverse_bigO_transfer P hshape hmass hβ hρ hq hrr hqr
  have hrem := source_density_physical_site_remainder P hshape hmass hreg hβ hρ hr hr₀
  exact (hdiff.add hrem).congr_left (fun ε => by ring)

end TimeTraps.Interval
