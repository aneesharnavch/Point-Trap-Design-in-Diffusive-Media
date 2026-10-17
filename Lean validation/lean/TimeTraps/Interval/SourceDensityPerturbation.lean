module

public import TimeTraps.Analysis.SourceCoordinate
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-! Uniform second-order coefficient expansions and the actual normalized
source coordinate. The remainder hypothesis is precisely the uniform
coefficient Taylor hypothesis of the stationary-density perturbation
subsection. Exact normalization is only required near parameter zero. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter Asymptotics TimeTraps.Analysis
open scoped Topology

def SourceUniformExpansion (f : ℝ → ℝ → ℝ) (f₀ f₁ : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ Icc (0 : ℝ) 1,
    |f ε x - f₀ x - ε * f₁ x| ≤ C * ε ^ 2

theorem source_uniform_expansion_derivative {f : ℝ → ℝ → ℝ} {f₀ f₁ : ℝ → ℝ}
    (hf : SourceUniformExpansion f f₀ f₁) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun ε => f ε x) (f₁ x) 0 := by
  obtain ⟨C, _, hC⟩ := hf
  have hzero : f 0 x = f₀ x := by
    have h := hC.self_of_nhds x hx
    have he : |f 0 x - f₀ x| ≤ 0 := by simpa using h
    have hh := abs_le.mp he
    linarith
  have hb : (fun ε : ℝ => f ε x - f₀ x - ε * f₁ x) =O[𝓝 0] (fun ε => ε ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards [hC] with ε hε
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hε x hx
  have hl := hb.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) (by decide : 1 < 2))
  apply HasDerivAt.of_isLittleO
  simpa only [hzero, sub_zero, smul_eq_mul] using hl

theorem source_density_coordinate_expansion (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β) :
    SourceUniformExpansion (fun ε => (P ε).coordinate) (P 0).coordinate
      (fun x => ∫ t in (0 : ℝ)..x, β t) := by
  obtain ⟨C, hC, hr⟩ := hρ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmass, hr] with ε hε hrε
  intro x hx
  have hs : uIcc (0 : ℝ) x ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have hc (e : ℝ) : ContinuousOn (P e).density (Icc (0 : ℝ) 1) := by
    simpa only [(hshape e).1, (hshape e).2] using (P e).continuous
  have hiε := ((hc ε).mono hs).intervalIntegrable (μ := volume)
  have hi₀ := ((hc 0).mono hs).intervalIntegrable (μ := volume)
  have hiβ := (hβ.mono hs).intervalIntegrable (μ := volume)
  have hid : (P ε).coordinate x - (P 0).coordinate x -
      ε * (∫ t in (0 : ℝ)..x, β t) =
      ∫ t in (0 : ℝ)..x, (P ε).density t - (P 0).density t - ε * β t := by
    rw [intervalIntegral.integral_sub (hiε.sub hi₀) (hiβ.const_mul ε),
      intervalIntegral.integral_sub hiε hi₀, intervalIntegral.integral_const_mul]
    simp only [SourceInterval.coordinate, (hshape ε).1, (hshape 0).1, hε,
      hmass.self_of_nhds, div_one]
  rw [hid]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := x)
    (C := C * ε ^ 2) (f := fun t => (P ε).density t - (P 0).density t - ε * β t)
    (fun t ht => by
      rw [uIoc_of_le hx.1] at ht
      simpa only [Real.norm_eq_abs] using hrε t ⟨ht.1.le, ht.2.trans hx.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] at hb
  exact hb.trans (mul_le_of_le_one_right (mul_nonneg hC (sq_nonneg ε)) hx.2)

theorem source_density_first_variation_mass_zero (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β) :
    (∫ t in (0 : ℝ)..1, β t) = 0 := by
  have hd := source_uniform_expansion_derivative
    (source_density_coordinate_expansion P hshape hmass hβ hρ)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  have he : (fun ε => (P ε).coordinate 1) = fun _ : ℝ => (1 : ℝ) := by
    funext ε
    simpa only [(hshape ε).2] using (P ε).coordinate_right
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (1 : ℝ))

end TimeTraps.Interval
