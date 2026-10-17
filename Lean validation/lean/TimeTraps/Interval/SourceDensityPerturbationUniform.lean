module

public import TimeTraps.Interval.SourceDensityPerturbationReciprocal
public import TimeTraps.Interval.SourceDensityPerturbationWeight
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! The uniform effective-weight expansion for a normalized perturbed
stationary medium. The actual moving inverse coordinate is retained.
Compactness and C1 spatial regularity provide every bound needed in the
product, composition, and reciprocal estimates. -/

namespace TimeTraps.Interval

open Set Filter TimeTraps.Analysis
open scoped Topology ContDiff

theorem source_density_effective_weight_expansion (A : ℝ → IntervalMedium)
    (hshape : ∀ ε, (A ε).source.left = 0 ∧ (A ε).source.right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (A ε).source.mass = 1)
    (hρ₀ : ContDiffOn ℝ 1 (A 0).source.density (Icc (0 : ℝ) 1))
    {α g : ℝ → ℝ} (hα : ContDiffOn ℝ 1 α (Icc (0 : ℝ) 1))
    (hg : ContDiffOn ℝ 1 g (Icc (0 : ℝ) 1))
    (ha : SourceUniformExpansion (fun ε => (A ε).conductance) (A 0).conductance
      (fun x => (A 0).conductance x * α x))
    (hρ : SourceUniformExpansion (fun ε => (A ε).source.density) (A 0).source.density
      (fun x => (A 0).source.density x * g x))
    {c : ℝ}
    (hbase : ∀ x ∈ Icc (0 : ℝ) 1, (A 0).conductance x * (A 0).source.density x = c) :
    SourceUniformExpansion (fun ε => (A ε).cellWeight.value) (fun _ => 1 / c)
      (fun y => -(α ((A 0).source.inverse y) + g ((A 0).source.inverse y)) / c) := by
  have hzero : (0 : ℝ) ∈ Icc (A 0).source.left (A 0).source.right := by
    simp only [(hshape 0).1, (hshape 0).2, mem_Icc]
    exact ⟨le_rfl, zero_le_one⟩
  have hc : 0 < c := by
    rw [← hbase 0 ⟨le_rfl, zero_le_one⟩]
    exact mul_pos ((A 0).conductance_pos 0 hzero) ((A 0).source.positive 0 hzero)
  have ha₀ : ContinuousOn (A 0).conductance (Icc (0 : ℝ) 1) := by
    simpa only [(hshape 0).1, (hshape 0).2] using (A 0).conductance_continuous
  have hβ := hρ₀.continuousOn.mul hg.continuousOn
  have hp := source_uniform_expansion_mul ha hρ ha₀ (ha₀.mul hα.continuousOn)
    hρ₀.continuousOn hβ
  have hprod : SourceUniformExpansion
      (fun ε x => (A ε).conductance x * (A ε).source.density x) (fun _ => c)
      (fun x => c * (α x + g x)) := by
    obtain ⟨C, hC, hpC⟩ := hp
    refine ⟨C, hC, ?_⟩
    filter_upwards [hpC] with ε hε
    intro x hx
    have he : (A ε).conductance x * (A ε).source.density x - c - ε * (c * (α x + g x)) =
        (A ε).conductance x * (A ε).source.density x -
          (A 0).conductance x * (A 0).source.density x -
          ε * ((A 0).conductance x * α x * (A 0).source.density x +
            (A 0).conductance x * ((A 0).source.density x * g x)) := by
      rw [← hbase x hx]
      ring
    change |(A ε).conductance x * (A ε).source.density x - c - ε * (c * (α x + g x))| ≤ _
    rw [he]
    exact hε x hx
  have hinv := source_density_inverse_expansion (fun ε => (A ε).source)
    hshape hmass hρ₀ hβ hρ
  have hiv := source_inverse_variation_continuous (A 0).source (hshape 0).1 (hshape 0).2 hβ
  have hqrange (ε y : ℝ) (_ : y ∈ Icc (0 : ℝ) 1) :
      (A ε).source.inverse y ∈ Icc (0 : ℝ) 1 := by
    simpa only [(hshape ε).1, (hshape ε).2] using (A ε).source.inverse_mem y
  have hcomp := source_uniform_expansion_comp_const hprod hinv hiv.continuousOn
    (contDiffOn_const.mul (hα.add hg)) hqrange
  have hfirst : Continuous (fun y => c * (α ((A 0).source.inverse y) + g ((A 0).source.inverse y))) :=
    ((continuousOn_const.mul (hα.continuousOn.add hg.continuousOn)).comp_continuous
      (A 0).source.inverse_continuous (fun y => by
        simpa only [(hshape 0).1, (hshape 0).2] using (A 0).source.inverse_mem y))
  obtain ⟨C, hC, hrec⟩ := source_uniform_expansion_inv_const hc hcomp hfirst.continuousOn
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrec, hmass] with ε hε hmε
  intro y hy
  have he := hε y hy
  have hw : (A ε).cellWeight.value y =
      1 / ((A ε).conductance ((A ε).source.inverse y) *
        (A ε).source.density ((A ε).source.inverse y)) := by
    change (A ε).source.mass ^ 2 / _ = _
    rw [hmε, one_pow]
  have hcoef : -(c * (α ((A 0).source.inverse y) + g ((A 0).source.inverse y))) / c ^ 2 =
      -(α ((A 0).source.inverse y) + g ((A 0).source.inverse y)) / c := by field_simp
  change |(A ε).cellWeight.value y - 1 / c -
    ε * (-(α ((A 0).source.inverse y) + g ((A 0).source.inverse y)) / c)| ≤ _
  rw [hw]
  simpa only [hcoef] using he

theorem source_density_effective_weight_derivative_closed (A : ℝ → IntervalMedium)
    (hshape : ∀ ε, (A ε).source.left = 0 ∧ (A ε).source.right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (A ε).source.mass = 1)
    (hρ₀ : ContDiffOn ℝ 1 (A 0).source.density (Icc (0 : ℝ) 1))
    {α g : ℝ → ℝ} (hα : ContDiffOn ℝ 1 α (Icc (0 : ℝ) 1))
    (hg : ContDiffOn ℝ 1 g (Icc (0 : ℝ) 1))
    (ha : SourceUniformExpansion (fun ε => (A ε).conductance) (A 0).conductance
      (fun x => (A 0).conductance x * α x))
    (hρ : SourceUniformExpansion (fun ε => (A ε).source.density) (A 0).source.density
      (fun x => (A 0).source.density x * g x))
    {c : ℝ}
    (hbase : ∀ x ∈ Icc (0 : ℝ) 1, (A 0).conductance x * (A 0).source.density x = c)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun ε => (A ε).cellWeight.value y)
      (-(α ((A 0).source.inverse y) + g ((A 0).source.inverse y)) / c) 0 :=
  source_uniform_expansion_derivative
    (source_density_effective_weight_expansion A hshape hmass hρ₀ hα hg ha hρ hbase) hy

end TimeTraps.Interval
