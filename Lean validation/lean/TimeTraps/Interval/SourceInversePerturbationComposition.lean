module

public import TimeTraps.Interval.SourceInversePerturbation

@[expose] public section

/-! First variations along moving coordinates. Uniform coefficient
remainders permit evaluation at a moving point, rather than assuming a
joint derivative of the parameter-dependent inverse. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter Asymptotics TimeTraps.Analysis
open scoped Topology

theorem source_uniform_expansion_moving_derivative {f : ℝ → ℝ → ℝ} {f₀ f₁ q : ℝ → ℝ}
    (hf : SourceUniformExpansion f f₀ f₁)
    (hqrange : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Icc (0 : ℝ) 1)
    {v d : ℝ} (hq : HasDerivAt q v 0) (hd : HasDerivAt f₀ d (q 0))
    (h₁ : ContinuousAt f₁ (q 0)) :
    HasDerivAt (fun ε => f ε (q ε)) (d * v + f₁ (q 0)) 0 := by
  obtain ⟨C, _, hC⟩ := hf
  have hz : f 0 (q 0) = f₀ (q 0) := by
    have h := hC.self_of_nhds (q 0) hqrange.self_of_nhds
    have he : |f 0 (q 0) - f₀ (q 0)| ≤ 0 := by simpa using h
    have hh := abs_le.mp he
    linarith
  have hr : (fun ε : ℝ => f ε (q ε) - f₀ (q ε) - ε * f₁ (q ε)) =o[𝓝 0] (fun ε => ε) := by
    apply (IsBigO.of_bound C ?_).trans_isLittleO
      (isLittleO_pow_id (𝕜 := ℝ) (by decide : 1 < 2))
    filter_upwards [hC, hqrange] with ε hε hqe
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hε (q ε) hqe
  have hb := (hd.comp 0 hq).isLittleO
  simp only [sub_zero, smul_eq_mul, Function.comp_apply] at hb
  have ht : Tendsto (fun ε => f₁ (q ε) - f₁ (q 0)) (𝓝 (0 : ℝ)) (𝓝 0) :=
    by simpa using (h₁.tendsto.comp hq.continuousAt.tendsto).sub_const (f₁ (q 0))
  have hc : (fun ε : ℝ => (f₁ (q ε) - f₁ (q 0)) * ε) =o[𝓝 0] (fun ε => ε) := by
    simpa only [one_mul] using ((isLittleO_one_iff ℝ).mpr ht).mul_isBigO
      (isBigO_refl (fun ε : ℝ => ε) (𝓝 0))
  apply HasDerivAt.of_isLittleO
  simpa only [sub_zero, smul_eq_mul] using
    ((hr.add hb).add hc).congr_left (fun ε => by rw [hz]; ring)

theorem source_inverse_variation_continuous (P : SourceInterval) (hl : P.left = 0)
    (hr : P.right = 1) {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1)) :
    Continuous (fun y => -(∫ t in (0 : ℝ)..P.inverse y, β t) / P.density (P.inverse y)) := by
  have hmem (y : ℝ) : P.inverse y ∈ Icc (0 : ℝ) 1 := by
    simpa only [hl, hr] using P.inverse_mem y
  have hH := integral_primitive_continuousOn (l := (0 : ℝ)) (r := 1) zero_le_one hβ
  have hnum := hH.comp_continuous P.inverse_continuous hmem
  have hden := P.continuous.comp_continuous P.inverse_continuous P.inverse_mem
  exact hnum.neg.div hden (fun y => ne_of_gt (P.positive _ (P.inverse_mem y)))

theorem source_density_moving_inverse_derivative (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    (hreg : ContDiffOn ℝ 1 (P 0).density (Icc (0 : ℝ) 1))
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β)
    {q : ℝ → ℝ} {v : ℝ} (hq : HasDerivAt q v 0) (hq₀ : q 0 ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => (P ε).inverse (q ε))
      ((v - ∫ t in (0 : ℝ)..(P 0).inverse (q 0), β t) /
        (P 0).density ((P 0).inverse (q 0))) 0 := by
  have hqin : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Ioo (0 : ℝ) 1 :=
    hq.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hq₀)
  have hqrange : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ∈ Icc (0 : ℝ) 1 :=
    hqin.mono (fun _ h => Ioo_subset_Icc_self h)
  have hd := (P 0).inverse_derivative hq₀
  rw [hmass.self_of_nhds] at hd
  have he := source_uniform_expansion_moving_derivative
    (source_density_inverse_expansion P hshape hmass hreg hβ hρ) hqrange hq hd
    (source_inverse_variation_continuous (P 0) (hshape 0).1 (hshape 0).2 hβ).continuousAt
  convert he using 1
  ring

end TimeTraps.Interval
