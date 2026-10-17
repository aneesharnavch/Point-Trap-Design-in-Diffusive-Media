module

public import TimeTraps.Interval.SourceInversePerturbationComposition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Interior regularity needed for the physical-position Taylor
composition. Both regularity assertions concern the already constructed
inverse and its already derived first-variation coefficient. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped ContDiff

theorem source_inverse_contDiff_two (P : SourceInterval)
    (hρ : ContDiffOn ℝ 1 P.density (Icc P.left P.right)) :
    ContDiffOn ℝ 2 P.inverse (Ioo (0 : ℝ) 1) := by
  have hdcont : Continuous (fun y => P.mass / P.density (P.inverse y)) :=
    continuous_const.div (P.continuous.comp_continuous P.inverse_continuous P.inverse_mem)
      (fun y => ne_of_gt (P.positive _ (P.inverse_mem y)))
  have h₁ : ContDiffOn ℝ 1 P.inverse (Ioo (0 : ℝ) 1) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun y hy => (P.inverse_derivative hy).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro he
      norm_num at he
    · apply (contDiffOn_zero.mpr hdcont.continuousOn).congr
      intro y hy
      exact (P.inverse_derivative hy).deriv
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun y hy => (P.inverse_derivative hy).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro he
    norm_num at he
  · have hden := hρ.comp h₁ (fun y _ => P.inverse_mem y)
    apply (contDiffOn_const.div hden (fun y _ => ne_of_gt (P.positive _ (P.inverse_mem y)))).congr
    intro y hy
    exact (P.inverse_derivative hy).deriv

theorem source_inverse_variation_contDiff_one (P : SourceInterval) (hl : P.left = 0)
    (hr : P.right = 1) (hρ : ContDiffOn ℝ 1 P.density (Icc (0 : ℝ) 1))
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 (fun y => -(∫ t in (0 : ℝ)..P.inverse y, β t) / P.density (P.inverse y))
      (Ioo (0 : ℝ) 1) := by
  have hH : ContDiffOn ℝ 1 (fun x => ∫ t in (0 : ℝ)..x, β t) (Ioo (0 : ℝ) 1) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun x hx => (integral_primitive_hasDerivAt hβ hx).differentiableAt.differentiableWithinAt,
      ?_, ?_⟩
    · intro he
      norm_num at he
    · apply (contDiffOn_zero.mpr (hβ.mono Ioo_subset_Icc_self)).congr
      intro x hx
      exact (integral_primitive_hasDerivAt hβ hx).deriv
  have hρ' : ContDiffOn ℝ 1 P.density (Icc P.left P.right) := by simpa only [hl, hr] using hρ
  have hi := (source_inverse_contDiff_two P hρ').of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hmap : MapsTo P.inverse (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) := by
    intro y hy
    simpa only [hl, hr] using P.inverse_interior hy
  have hnum := hH.comp hi hmap
  have hden := hρ'.comp hi (fun y _ => P.inverse_mem y)
  exact hnum.neg.div hden (fun y _ => ne_of_gt (P.positive _ (P.inverse_mem y)))

end TimeTraps.Interval
