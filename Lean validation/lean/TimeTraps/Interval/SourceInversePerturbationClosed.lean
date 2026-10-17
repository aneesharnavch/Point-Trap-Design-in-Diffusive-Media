module

public import TimeTraps.Interval.SourceInversePerturbationRegularity

@[expose] public section

/-! Closed-interval C1 regularity of the inverse coordinate. The
constant extension used to define the actual inverse need not be
differentiable at the endpoints. A C1 integral extension agrees with it
on the closed interval, proving the relative regularity required by the
perturbation profile and the affine comparison problem. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped ContDiff

theorem source_inverse_contDiff_one_closed (P : SourceInterval) :
    ContDiffOn ℝ 1 P.inverse (Icc (0 : ℝ) 1) := by
  let J : ℝ → ℝ := fun y => P.mass / P.density (P.inverse y)
  have hJ : Continuous J :=
    continuous_const.div (P.continuous.comp_continuous P.inverse_continuous P.inverse_mem)
      (fun y => ne_of_gt (P.positive _ (P.inverse_mem y)))
  let F : ℝ → ℝ := fun y => P.left + ∫ t in (0 : ℝ)..y, J t
  have hFd (y : ℝ) : HasDerivAt F (J y) y :=
    (intervalIntegral.integral_hasDerivAt_right (hJ.intervalIntegrable 0 y)
      hJ.stronglyMeasurable.stronglyMeasurableAtFilter hJ.continuousAt).const_add P.left
  have hF : ContDiff ℝ 1 F := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun y => (hFd y).differentiableAt, ?_⟩
    have he : deriv F = J := by funext y; exact (hFd y).deriv
    rw [he]
    exact hJ
  apply hF.contDiffOn.congr
  intro y hy
  have hi := integral_derivative_to_point P.inverse_continuous.continuousOn hJ.continuousOn
    (fun z hz => P.inverse_derivative hz) hy
  change P.inverse y = P.left + ∫ t in (0 : ℝ)..y, J t
  rw [hi, P.inverse_zero]
  ring

theorem source_density_perturbation_profile_contDiff (P : SourceInterval)
    (hl : P.left = 0) (hr : P.right = 1) {α g : ℝ → ℝ}
    (hα : ContDiffOn ℝ 1 α (Icc (0 : ℝ) 1))
    (hg : ContDiffOn ℝ 1 g (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 (fun y => -(α (P.inverse y) + g (P.inverse y))) (Icc (0 : ℝ) 1) := by
  apply (hα.add hg).neg.comp (source_inverse_contDiff_one_closed P)
  intro y _
  simpa only [hl, hr] using P.inverse_mem y

end TimeTraps.Interval
