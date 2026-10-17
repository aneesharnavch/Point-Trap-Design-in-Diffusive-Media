module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Supporting tangent inequalities, with strictness away from the point of
tangency. These are exact secant/derivative comparisons. -/

namespace TimeTraps.Analysis

open Set

theorem concave_tangent_le {S : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hf : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d y) :
    f x ≤ f y + d * (x - y) := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hf.le_slope_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    linarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    linarith

theorem strictConcave_tangent_lt {S : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hf : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hd : HasDerivAt f d y) (hne : x ≠ y) :
    f x < f y + d * (x - y) := by
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have h := hf.lt_slope_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at h
    have hh := (lt_div_iff₀ (sub_pos.mpr hxy)).mp h
    linarith
  · have h := hf.slope_lt_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at h
    have hh := (div_lt_iff₀ (sub_pos.mpr hyx)).mp h
    linarith

theorem strictConcave_tangent_eq_iff {S : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hf : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d y) :
    f x = f y + d * (x - y) ↔ x = y := by
  constructor
  · intro he
    by_contra hne
    exact (strictConcave_tangent_lt hf hx hy hd hne).ne he
  · rintro rfl
    simp

end TimeTraps.Analysis
