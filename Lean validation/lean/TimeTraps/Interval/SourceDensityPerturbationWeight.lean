module

public import TimeTraps.Interval.SourceInversePerturbationComposition
public import TimeTraps.Interval.StrictPartition
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-! The first variation of the actual effective resistance. Both the
conductance and density are evaluated at the moving inverse source
coordinate. Constancy of the baseline product cancels its spatial
derivative; that cancellation is proved rather than omitted. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology ContDiff

theorem source_density_product_derivative {a ρ : ℝ → ℝ → ℝ} {α g : ℝ → ℝ}
    (ha : SourceUniformExpansion a (a 0) (fun x => a 0 x * α x))
    (hρ : SourceUniformExpansion ρ (ρ 0) (fun x => ρ 0 x * g x))
    {x c : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hc : a 0 x * ρ 0 x = c) :
    HasDerivAt (fun ε => a ε x * ρ ε x) (c * (α x + g x)) 0 := by
  have hd := (source_uniform_expansion_derivative ha hx).mul
    (source_uniform_expansion_derivative hρ hx)
  convert! hd using 1
  rw [← hc]
  ring

theorem source_density_effective_weight_derivative (A : ℝ → IntervalMedium)
    (hshape : ∀ ε, (A ε).source.left = 0 ∧ (A ε).source.right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (A ε).source.mass = 1)
    (ha₀ : ContDiffOn ℝ 1 (A 0).conductance (Icc (0 : ℝ) 1))
    (hρ₀ : ContDiffOn ℝ 1 (A 0).source.density (Icc (0 : ℝ) 1))
    {α g : ℝ → ℝ} (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (ha : SourceUniformExpansion (fun ε => (A ε).conductance) (A 0).conductance
      (fun x => (A 0).conductance x * α x))
    (hρ : SourceUniformExpansion (fun ε => (A ε).source.density) (A 0).source.density
      (fun x => (A 0).source.density x * g x))
    {c : ℝ} (hc : 0 < c)
    (hbase : ∀ x ∈ Icc (0 : ℝ) 1, (A 0).conductance x * (A 0).source.density x = c)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => (A ε).cellWeight.value y)
      (-(α ((A 0).source.inverse y) + g ((A 0).source.inverse y)) / c) 0 := by
  let q : ℝ → ℝ := fun ε => (A ε).source.inverse y
  let x := q 0
  let Z := -(∫ t in (0 : ℝ)..x, (A 0).source.density t * g t) / (A 0).source.density x
  have hβ := hρ₀.continuousOn.mul hg
  have hq : HasDerivAt q Z 0 := source_density_inverse_derivative
    (fun ε => (A ε).source) hshape hmass hρ₀ hβ hρ (Ioo_subset_Icc_self hy)
  have hqr : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun ε => by
      simpa only [(hshape ε).1, (hshape ε).2] using (A ε).source.inverse_mem y)
  have hx : x ∈ Ioo (0 : ℝ) 1 := by
    simpa only [(hshape 0).1, (hshape 0).2] using (A 0).source.inverse_interior hy
  have hxnhds : Icc (0 : ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  have had := (ha₀.contDiffAt hxnhds).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hρd := (hρ₀.contDiffAt hxnhds).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have ham := source_uniform_expansion_moving_derivative ha hqr hq had.hasDerivAt
    ((ha₀.continuousOn.mul hα).continuousAt hxnhds)
  have hρm := source_uniform_expansion_moving_derivative hρ hqr hq hρd.hasDerivAt
    (hβ.continuousAt hxnhds)
  have hconst : HasDerivAt (fun t => (A 0).conductance t * (A 0).source.density t) 0 x := by
    apply (hasDerivAt_const x c).congr_of_eventuallyEq
    filter_upwards [hxnhds] with t ht
    exact hbase t ht
  have hcancel := (had.hasDerivAt.mul hρd.hasDerivAt).unique hconst
  have hbase₀ := hbase x (Ioo_subset_Icc_self hx)
  have hprod : HasDerivAt (fun ε => (A ε).conductance (q ε) * (A ε).source.density (q ε))
      (c * (α x + g x)) 0 := by
    convert! ham.mul hρm using 1
    change c * (α x + g x) =
      (deriv (A 0).conductance x * Z + (A 0).conductance x * α x) * (A 0).source.density x +
      (A 0).conductance x * (deriv (A 0).source.density x * Z + (A 0).source.density x * g x)
    calc
      _ = Z * 0 + c * (α x + g x) := by ring
      _ = Z * (deriv (A 0).conductance x * (A 0).source.density x +
        (A 0).conductance x * deriv (A 0).source.density x) +
        ((A 0).conductance x * (A 0).source.density x) * (α x + g x) := by rw [hcancel, hbase₀]
      _ = _ := by ring
  have hi := hprod.inv (show (A 0).conductance (q 0) * (A 0).source.density (q 0) ≠ 0 from
    by change (A 0).conductance x * (A 0).source.density x ≠ 0; rw [hbase₀]; exact ne_of_gt hc)
  have he : (fun ε => (A ε).cellWeight.value y) =ᶠ[𝓝 (0 : ℝ)]
      (fun ε => ((A ε).conductance (q ε) * (A ε).source.density (q ε))⁻¹) := by
    filter_upwards [hmass] with ε hε
    change (A ε).source.mass ^ 2 /
      ((A ε).conductance (q ε) * (A ε).source.density (q ε)) = _
    rw [hε, one_pow, one_div]
  have hit := hi.congr_of_eventuallyEq he
  convert! hit using 1
  change -(α x + g x) / c =
    -(c * (α x + g x)) / ((A 0).conductance x * (A 0).source.density x) ^ 2
  rw [hbase₀]
  field_simp

end TimeTraps.Interval
