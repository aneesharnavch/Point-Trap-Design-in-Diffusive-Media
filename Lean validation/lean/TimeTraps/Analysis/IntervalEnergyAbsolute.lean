module

public import TimeTraps.Analysis.PositiveQuotient
public import TimeTraps.Analysis.IntervalPointForm
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Absolute value preserves the actual one-dimensional energy space and
its derivative-square energy. Consequently it preserves the quadratic
point form even for arbitrary real contact strengths. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

theorem interval_absolutelyContinuous_abs {u : ℝ → ℝ} {l r : ℝ}
    (hu : AbsolutelyContinuousOnInterval u l r) :
    AbsolutelyContinuousOnInterval (fun x => |u x|) l r := by
  apply interval_absolutelyContinuous_of_dist_le hu (show (0 : ℝ) ≤ 1 by norm_num)
  intro x _ y _
  simpa only [one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub (u x) (u y)

/-- At zeros both derivatives vanish almost everywhere: absolute value and
the difference `|u| - u` have local minima there. -/
theorem IntervalEnergy.abs_derivative_norm_ae {u : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) :
    ∀ᵐ x ∂volume.restrict (uIoc l r),
      ‖deriv (fun y => |u y|) x‖ = ‖deriv u x‖ := by
  have ha := interval_absolutelyContinuous_abs hu.absolutelyContinuous
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [hu.absolutelyContinuous.ae_differentiableAt,
    ha.ae_differentiableAt] with x hux hax hx
  have hd := hux (uIoc_subset_uIcc hx)
  have had := hax (uIoc_subset_uIcc hx)
  rcases lt_trichotomy (u x) 0 with hn | hz | hp
  · have he := ((hasDerivAt_abs_neg hn).comp x hd.hasDerivAt).deriv
    simpa only [Function.comp_def, neg_one_mul, norm_neg] using congrArg norm he
  · have hmin : IsLocalMin (fun y => |u y|) x := by
      apply Filter.Eventually.of_forall
      intro y
      simpa only [hz, abs_zero] using abs_nonneg (u y)
    have hdiff : IsLocalMin (fun y => |u y| - u y) x := by
      apply Filter.Eventually.of_forall
      intro y
      simpa only [hz, abs_zero, sub_zero] using sub_nonneg.mpr (le_abs_self (u y))
    have hza := hmin.deriv_eq_zero
    have hzu := hdiff.hasDerivAt_eq_zero (had.hasDerivAt.sub hd.hasDerivAt)
    rw [hza] at hzu
    have hzero : deriv u x = 0 := by linarith
    rw [hza, hzero]
  · have he := ((hasDerivAt_abs_pos hp).comp x hd.hasDerivAt).deriv
    simpa only [Function.comp_def, one_mul] using congrArg norm he

theorem IntervalEnergy.abs_derivative_square_ae {u : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) :
    (fun x => deriv (fun y => |u y|) x ^ 2) =ᵐ[volume.restrict (uIoc l r)]
      (fun x => deriv u x ^ 2) := by
  filter_upwards [hu.abs_derivative_norm_ae] with x hx
  have hs := congrArg (fun t : ℝ => t ^ 2) hx
  change |deriv (fun y => |u y|) x| ^ 2 = |deriv u x| ^ 2 at hs
  simpa only [sq_abs] using hs

theorem IntervalEnergy.abs {u : ℝ → ℝ} {l r : ℝ} (hu : IntervalEnergy u l r) :
    IntervalEnergy (fun x => |u x|) l r := by
  refine ⟨interval_absolutelyContinuous_abs hu.absolutelyContinuous, ?_⟩
  apply intervalIntegrable_iff.mpr
  exact (hu.derivative_memLp.of_le
    (aestronglyMeasurable_deriv (fun x => |u x|) _)
    (hu.abs_derivative_norm_ae.mono fun _ hx => hx.le)).integrable_sq

theorem IntervalEnergy.abs_derivative_energy {u : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) :
    (∫ x in l..r, deriv (fun y => |u y|) x ^ 2) = ∫ x in l..r, deriv u x ^ 2 :=
  intervalIntegral.integral_congr_ae_restrict hu.abs_derivative_square_ae

theorem interval_abs_square_mass (u : ℝ → ℝ) (l r : ℝ) :
    (∫ x in l..r, |u x| ^ 2) = ∫ x in l..r, u x ^ 2 := by
  simp only [sq_abs]

theorem IntervalEnergy.abs_point_form {ι : Type*} [Fintype ι]
    {u : ℝ → ℝ} {l r : ℝ} (hu : IntervalEnergy u l r) (D : ℝ) (κ z : ι → ℝ) :
    intervalPointForm D κ z l r (fun x => |u x|) (fun x => |u x|) =
      intervalPointForm D κ z l r u u := by
  simp only [intervalPointForm_self, hu.abs_derivative_energy, sq_abs]

end TimeTraps.Analysis
