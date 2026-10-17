module

public import TimeTraps.Interval.SourceDensityPerturbation

@[expose] public section

/-! Quantitative primitive and inverse-coordinate bounds. These lemmas
use explicit constants; the family theorem obtains those constants from
smoothness and positivity on the compact physical interval. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

theorem source_primitive_increment {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..x, f t) - (∫ t in (0 : ℝ)..y, f t) = ∫ t in y..x, f t := by
  have h₁ := (hf.mono (uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
    ⟨le_rfl, zero_le_one⟩) hy)).intervalIntegrable (μ := volume)
  have h₂ := (hf.mono (uIcc_subset_Icc hy hx)).intervalIntegrable (μ := volume)
  have he := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  linarith

theorem source_primitive_difference_bound {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) {B : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ B)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |(∫ t in (0 : ℝ)..x, f t) - (∫ t in (0 : ℝ)..y, f t)| ≤ B * |x - y| := by
  rw [source_primitive_increment hf hx hy]
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x) (f := f) (C := B)
      (fun t ht => by
        simpa only [Real.norm_eq_abs] using hb t (uIcc_subset_Icc hy hx (uIoc_subset_uIcc ht)))

theorem source_coordinate_taylor_bound (P : SourceInterval) (hl : P.left = 0)
    (hr : P.right = 1) (hm : P.mass = 1) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |P.density x - P.density y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |P.coordinate x - P.coordinate y - P.density y * (x - y)| ≤ L * |x - y| ^ 2 := by
  have hc : ContinuousOn P.density (Icc (0 : ℝ) 1) := by
    simpa only [hl, hr] using P.continuous
  have hi := (hc.mono (uIcc_subset_Icc hy hx)).intervalIntegrable (μ := volume)
  have he : P.coordinate x - P.coordinate y - P.density y * (x - y) =
      ∫ t in y..x, P.density t - P.density y := by
    simp only [SourceInterval.coordinate, hl, hm, div_one]
    rw [source_primitive_increment hc hx hy,
      intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x)
    (C := L * |x - y|) (f := fun t => P.density t - P.density y) (fun t ht => by
      rw [Real.norm_eq_abs]
      exact (hlip t (uIcc_subset_Icc hy hx (uIoc_subset_uIcc ht)) y hy).trans
        (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc ht)) hL))
  simpa only [Real.norm_eq_abs, mul_assoc, ← sq] using hb

theorem source_coordinate_lower_bound (P : SourceInterval) (hl : P.left = 0)
    (hr : P.right = 1) (hm : P.mass = 1) {m : ℝ}
    (hmin : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ P.density t)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    m * |x - y| ≤ |P.coordinate x - P.coordinate y| := by
  have hc : ContinuousOn P.density (Icc (0 : ℝ) 1) := by
    simpa only [hl, hr] using P.continuous
  have hinc (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
      (hst : s ≤ t) : m * (t - s) ≤ P.coordinate t - P.coordinate s := by
    have hi := (hc.mono (uIcc_subset_Icc hs ht)).intervalIntegrable (μ := volume)
    have hb := intervalIntegral.integral_mono_on hst
      (show IntervalIntegrable (fun _ : ℝ => m) volume s t from intervalIntegrable_const) hi
      (fun u hu => hmin u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hb
    have hp := P.mass_fraction (by simpa only [hl, hr] using hs)
      (by simpa only [hl, hr] using ht) hst
    rw [hm, one_mul] at hp
    rw [hp] at hb
    nlinarith
  have hmono : MonotoneOn P.coordinate (Icc (0 : ℝ) 1) := by
    simpa only [hl, hr] using P.coordinate_strictMono.monotoneOn
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (hmono hx hy hxy))]
    nlinarith [hinc x y hx hy hxy]
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (hmono hy hx hyx))]
    exact hinc y x hy hx hyx

end TimeTraps.Interval
