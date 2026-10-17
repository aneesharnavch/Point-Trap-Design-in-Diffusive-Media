module

public import TimeTraps.Analysis.SignedIntervalPointOrderSolution

@[expose] public section

/-! Order preservation of the actual shifted resolvent follows by applying
positivity to the difference of the forcing terms. Both the original L2
almost-everywhere order and the closed-interval representative order are
retained, for arbitrary signed finite point strengths. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.shiftedInverse_mono_ae
    (P : SignedIntervalPointProblem ι l r) (f g : IntervalSobolevL2 l r)
    (hfg : ∀ᵐ x ∂volume.restrict (Ioo l r), f x ≤ g x) :
    ∀ᵐ x ∂volume.restrict (Ioo l r), P.shiftedInverse f x ≤ P.shiftedInverse g x := by
  have hp : ∀ᵐ x ∂volume.restrict (Ioo l r), 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  have hi := P.shiftedInverse_nonneg_ae (g - f) hp
  rw [map_sub] at hi
  filter_upwards [hi, Lp.coeFn_sub (P.shiftedInverse g) (P.shiftedInverse f)] with x hx he
  apply sub_nonneg.mp
  simpa only [he, Pi.sub_apply] using hx

theorem SignedIntervalPointProblem.shiftedSolution_representative_mono
    (P : SignedIntervalPointProblem ι l r) (f g : IntervalSobolevL2 l r)
    (hfg : ∀ᵐ x ∂volume.restrict (Ioo l r), f x ≤ g x) :
    ∀ x ∈ Icc l r, (P.shiftedSolution f).representative P.interval_pos x ≤
      (P.shiftedSolution g).representative P.interval_pos x := by
  have hp : ∀ᵐ x ∂volume.restrict (Ioo l r), 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro x hx
  have hi := P.shiftedSolution_representative_nonneg (g - f) hp x hx
  change 0 ≤ evalL P.interval_pos x hx (P.shiftedSolution (g - f)) at hi
  rw [map_sub P.shiftedSolution g f, map_sub] at hi
  exact sub_nonneg.mp hi

end TimeTraps.Analysis
