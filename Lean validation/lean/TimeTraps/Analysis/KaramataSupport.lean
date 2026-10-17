module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

/-! Supporting slopes on a finite set of values.  These statements need only
convexity, including when a value is an endpoint of the convex domain. -/

namespace TimeTraps.Analysis

open Set

theorem finite_slope_separator (L R : Finset ℝ)
    (h : ∀ l ∈ L, ∀ r ∈ R, l ≤ r) :
    ∃ c : ℝ, (∀ l ∈ L, l ≤ c) ∧ ∀ r ∈ R, c ≤ r := by
  classical
  by_cases hL : L.Nonempty
  · refine ⟨L.max' hL, fun l hl => L.le_max' l hl, ?_⟩
    exact fun r hr => h _ (L.max'_mem hL) r hr
  · by_cases hR : R.Nonempty
    · refine ⟨R.min' hR, ?_, fun r hr => R.min'_le r hr⟩
      exact fun l hl => (hL ⟨l, hl⟩).elim
    · exact ⟨0, fun l hl => (hL ⟨l, hl⟩).elim,
        fun r hr => (hR ⟨r, hr⟩).elim⟩

theorem finite_strict_slope_separator (L R : Finset ℝ)
    (h : ∀ l ∈ L, ∀ r ∈ R, l < r) :
    ∃ c : ℝ, (∀ l ∈ L, l < c) ∧ ∀ r ∈ R, c < r := by
  classical
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · obtain ⟨c, hcL, hcR⟩ := exists_between
        (h _ (L.max'_mem hL) _ (R.min'_mem hR))
      exact ⟨c, fun l hl => (L.le_max' l hl).trans_lt hcL,
        fun r hr => hcR.trans_le (R.min'_le r hr)⟩
    · refine ⟨L.max' hL + 1, ?_, fun r hr => (hR ⟨r, hr⟩).elim⟩
      intro l hl
      have := L.le_max' l hl
      linarith
  · by_cases hR : R.Nonempty
    · refine ⟨R.min' hR - 1, fun l hl => (hL ⟨l, hl⟩).elim, ?_⟩
      intro r hr
      have := R.min'_le r hr
      linarith
    · exact ⟨0, fun l hl => (hL ⟨l, hl⟩).elim,
        fun r hr => (hR ⟨r, hr⟩).elim⟩

theorem convex_finite_support_exists {S : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ S f) (T : Finset ℝ) (hT : ∀ z ∈ T, z ∈ S)
    {a : ℝ} (_ha : a ∈ S) :
    ∃ c : ℝ, ∀ z ∈ T, f a + c * (z - a) ≤ f z := by
  classical
  let L := (T.filter (fun z => z < a)).image (fun z => (f a - f z) / (a - z))
  let R := (T.filter (fun z => a < z)).image (fun z => (f z - f a) / (z - a))
  have hsep : ∀ l ∈ L, ∀ r ∈ R, l ≤ r := by
    intro l hl r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    exact hf.slope_mono_adjacent (hT u hu'.1) (hT v hv'.1) hu'.2 hv'.2
  obtain ⟨c, hcL, hcR⟩ := finite_slope_separator L R hsep
  refine ⟨c, ?_⟩
  intro z hz
  rcases lt_trichotomy z a with hza | rfl | haz
  · have hs := hcL _ (Finset.mem_image.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, hza⟩, rfl⟩)
    have hh := (div_le_iff₀ (sub_pos.mpr hza)).mp hs
    nlinarith
  · simp
  · have hs := hcR _ (Finset.mem_image.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, haz⟩, rfl⟩)
    have hh := (le_div_iff₀ (sub_pos.mpr haz)).mp hs
    linarith

theorem strictConvex_finite_support_exists {S : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ S f) (T : Finset ℝ) (hT : ∀ z ∈ T, z ∈ S)
    {a : ℝ} (_ha : a ∈ S) :
    ∃ c : ℝ, ∀ z ∈ T, z ≠ a → f a + c * (z - a) < f z := by
  classical
  let L := (T.filter (fun z => z < a)).image (fun z => (f a - f z) / (a - z))
  let R := (T.filter (fun z => a < z)).image (fun z => (f z - f a) / (z - a))
  have hsep : ∀ l ∈ L, ∀ r ∈ R, l < r := by
    intro l hl r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    exact hf.slope_strict_mono_adjacent (hT u hu'.1) (hT v hv'.1) hu'.2 hv'.2
  obtain ⟨c, hcL, hcR⟩ := finite_strict_slope_separator L R hsep
  refine ⟨c, ?_⟩
  intro z hz hne
  rcases lt_or_gt_of_ne hne with hza | haz
  · have hs := hcL _ (Finset.mem_image.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, hza⟩, rfl⟩)
    have hh := (div_lt_iff₀ (sub_pos.mpr hza)).mp hs
    nlinarith
  · have hs := hcR _ (Finset.mem_image.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, haz⟩, rfl⟩)
    have hh := (lt_div_iff₀ (sub_pos.mpr haz)).mp hs
    linarith

theorem finite_support_monotoneOn {T : Set ℝ} {f c : ℝ → ℝ}
    (hc : ∀ a ∈ T, ∀ z ∈ T, f a + c a * (z - a) ≤ f z) :
    MonotoneOn c T := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  · have h₁ := hc a ha b hb
    have h₂ := hc b hb a ha
    have hh : (c a - c b) * (b - a) ≤ 0 := by nlinarith
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_left hh (sub_pos.mpr hab))

end TimeTraps.Analysis
