module

public import TimeTraps.Interval.SourceInversePerturbationBounds

@[expose] public section

/-! A derived, uniform expansion of the actual inverse source coordinate.
The coefficient remainder is an input; an inverse expansion is not. The
positive lower bound and all spatial bounds are obtained from compactness
and C1 regularity of the baseline density. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology

theorem source_density_inverse_expansion (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    (hreg : ContDiffOn ℝ 1 (P 0).density (Icc (0 : ℝ) 1))
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β) :
    SourceUniformExpansion (fun ε => (P ε).inverse) (P 0).inverse
      (fun y => -(∫ t in (0 : ℝ)..(P 0).inverse y, β t) /
        (P 0).density ((P 0).inverse y)) := by
  let H : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, β t
  have hc : ContinuousOn (P 0).density (Icc (0 : ℝ) 1) := hreg.continuousOn
  obtain ⟨z, hz, hzmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hc
  let m := (P 0).density z
  have hm : 0 < m := (P 0).positive z (by simpa only [(hshape 0).1, (hshape 0).2] using hz)
  have hmin : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ (P 0).density t := fun _ ht => hzmin ht
  obtain ⟨L, hLip⟩ := hreg.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 1) isCompact_Icc
  have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |(P 0).density x - (P 0).density y| ≤ (L : ℝ) * |x - y| := by
    intro x hx y hy
    simpa only [Real.dist_eq] using hLip.dist_le_mul x hx y hy
  obtain ⟨b, hb, hbmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hβ.abs
  let B := |β b|
  have hB : 0 ≤ B := abs_nonneg _
  have hbβ : ∀ t ∈ Icc (0 : ℝ) 1, |β t| ≤ B := fun _ ht => hbmax ht
  have hH (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |H x| ≤ B := by
    have he := source_primitive_difference_bound hβ hbβ hx
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    simp only [intervalIntegral.integral_same, sub_zero, abs_of_nonneg hx.1] at he
    exact he.trans (mul_le_of_le_one_right hB hx.2)
  obtain ⟨C, hC, hr⟩ := source_density_coordinate_expansion P hshape hmass hβ hρ
  let A := (B + C) / m
  have hA : 0 ≤ A := div_nonneg (add_nonneg hB hC) hm.le
  have hAm : m * A = B + C := by dsimp [A]; field_simp
  let T := C + (L : ℝ) * A ^ 2 + B * A
  have hT : 0 ≤ T := add_nonneg (add_nonneg hC (mul_nonneg hL (sq_nonneg A))) (mul_nonneg hB hA)
  refine ⟨T / m, div_nonneg hT hm.le, ?_⟩
  have heps : ∀ᶠ ε : ℝ in 𝓝 0, |ε| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with ε hε
    have h : |ε| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
    exact h.le
  filter_upwards [hr, heps] with ε hrε hε
  intro y hy
  let x := (P ε).inverse y
  let x₀ := (P 0).inverse y
  have hx : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [(hshape ε).1, (hshape ε).2] using (P ε).inverse_mem y
  have hx₀ : x₀ ∈ Icc (0 : ℝ) 1 := by
    simpa only [(hshape 0).1, (hshape 0).2] using (P 0).inverse_mem y
  have hex : (P ε).coordinate x = y := (P ε).coordinate_inverse hy
  have hex₀ : (P 0).coordinate x₀ = y := (P 0).coordinate_inverse hy
  have hrx : |y - (P 0).coordinate x - ε * H x| ≤ C * ε ^ 2 := by
    simpa only [hex] using hrε x hx
  have hprod : |ε * H x| ≤ |ε| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hH x hx) (abs_nonneg ε)
  have heps₂ : ε ^ 2 ≤ |ε| := by nlinarith [sq_abs ε, abs_nonneg ε]
  have hcoord : |(P 0).coordinate x - (P 0).coordinate x₀| ≤ (B + C) * |ε| := by
    rw [hex₀]
    have ht := abs_le.mp hrx
    have hp := abs_le.mp hprod
    have hquad := mul_le_mul_of_nonneg_left heps₂ hC
    apply abs_le.mpr
    constructor <;> nlinarith
  have hdisp : |x - x₀| ≤ A * |ε| := by
    have hlower := source_coordinate_lower_bound (P 0) (hshape 0).1 (hshape 0).2
      hmass.self_of_nhds hmin hx hx₀
    have hd := hlower.trans hcoord
    nlinarith [mul_nonneg (le_of_lt hm) (abs_nonneg (x - x₀))]
  have htaylor := source_coordinate_taylor_bound (P 0) (hshape 0).1 (hshape 0).2
    hmass.self_of_nhds hL hlip hx hx₀
  have hHd : |H x - H x₀| ≤ B * |x - x₀| := source_primitive_difference_bound hβ hbβ hx hx₀
  let q := (P 0).density x₀
  have hq : 0 < q := hm.trans_le (hmin x₀ hx₀)
  have hqmin : m ≤ q := hmin x₀ hx₀
  have hsum : |q * (x - x₀) + ε * H x₀| ≤
      C * ε ^ 2 + (L : ℝ) * |x - x₀| ^ 2 + |ε| * B * |x - x₀| := by
    have hid : q * (x - x₀) + ε * H x₀ =
      -((y - (P 0).coordinate x - ε * H x) +
        ((P 0).coordinate x - (P 0).coordinate x₀ - q * (x - x₀)) +
        ε * (H x - H x₀)) := by rw [hex₀]; ring
    rw [hid, abs_neg]
    have hp : |ε * (H x - H x₀)| ≤ |ε| * B * |x - x₀| := by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left hHd (abs_nonneg ε)
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hrx htaylor)) hp)
  have hsum' : |q * (x - x₀) + ε * H x₀| ≤ T * ε ^ 2 := by
    have hd₂ : |x - x₀| ^ 2 ≤ A ^ 2 * ε ^ 2 := by
      have hs := mul_self_le_mul_self (abs_nonneg (x - x₀)) hdisp
      simpa only [← sq, mul_pow, sq_abs] using hs
    have hL₂ := mul_le_mul_of_nonneg_left hd₂ hL
    have hB₂ := mul_le_mul_of_nonneg_left hdisp (mul_nonneg (abs_nonneg ε) hB)
    have he : |ε| * B * (A * |ε|) = B * A * ε ^ 2 := by
      calc
        _ = B * A * |ε| ^ 2 := by ring
        _ = _ := by rw [sq_abs]
    rw [he] at hB₂
    dsimp only [T]
    nlinarith
  have hid : x - x₀ - ε * (-H x₀ / q) = (q * (x - x₀) + ε * H x₀) / q := by
    field_simp
    ring
  change |x - x₀ - ε * (-H x₀ / q)| ≤ T / m * ε ^ 2
  rw [hid, abs_div, abs_of_pos hq]
  apply (div_le_iff₀ hq).mpr
  have hrat : T * ε ^ 2 ≤ (T / m * ε ^ 2) * q := by
    have htm : T / m * m = T := div_mul_cancel₀ T (ne_of_gt hm)
    have hp := mul_le_mul_of_nonneg_left hqmin (mul_nonneg (div_nonneg hT hm.le) (sq_nonneg ε))
    nlinarith
  exact hsum'.trans hrat

theorem source_density_inverse_derivative (P : ℝ → SourceInterval)
    (hshape : ∀ ε, (P ε).left = 0 ∧ (P ε).right = 1)
    (hmass : ∀ᶠ ε in 𝓝 (0 : ℝ), (P ε).mass = 1)
    (hreg : ContDiffOn ℝ 1 (P 0).density (Icc (0 : ℝ) 1))
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hρ : SourceUniformExpansion (fun ε => (P ε).density) (P 0).density β)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun ε => (P ε).inverse y)
      (-(∫ t in (0 : ℝ)..(P 0).inverse y, β t) / (P 0).density ((P 0).inverse y)) 0 :=
  source_uniform_expansion_derivative
    (source_density_inverse_expansion P hshape hmass hreg hβ hρ) hy

end TimeTraps.Interval
