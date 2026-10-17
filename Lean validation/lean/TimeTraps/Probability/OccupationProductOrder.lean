module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

@[expose] public section

/-! Splitting a finite time square into its two strict chronological
triangles. The diagonal is removed using the time measure's genuine
absence of atoms. The integrand may have either sign. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter

noncomputable def orderedTimeIntegral (ν : Measure ℝ) (H : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p, if p.1 < p.2 then H p else 0 ∂ν.prod ν

theorem orderedTimeIntegral_eq_iterated (ν : Measure ℝ) [SFinite ν]
    {H : ℝ × ℝ → ℝ} (hH : Integrable H (ν.prod ν)) :
    orderedTimeIntegral ν H = ∫ s, ∫ t, if s < t then H (s, t) else 0 ∂ν ∂ν := by
  exact integral_prod _ (hH.indicator (measurableSet_lt measurable_fst measurable_snd))

theorem timePair_ne_ae (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ p ∂ν.prod ν, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Eventually.of_forall (fun s => (ν.ae_ne s).mono (fun _ h => Ne.symm h))

theorem integral_timeSquare_eq_ordered (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    {H : ℝ × ℝ → ℝ} (hH : Integrable H (ν.prod ν)) :
    (∫ p, H p ∂ν.prod ν) = orderedTimeIntegral ν H +
      orderedTimeIntegral ν (H ∘ Prod.swap) := by
  let U : ℝ × ℝ → ℝ := fun p => if p.1 < p.2 then H p else 0
  let L : ℝ × ℝ → ℝ := fun p => if p.2 < p.1 then H p else 0
  have hu : Integrable U (ν.prod ν) :=
    hH.indicator (measurableSet_lt measurable_fst measurable_snd)
  have hl : Integrable L (ν.prod ν) :=
    hH.indicator (measurableSet_lt measurable_snd measurable_fst)
  have he : H =ᵐ[ν.prod ν] fun p => U p + L p := (timePair_ne_ae ν).mono (by
    intro p hp
    rcases lt_or_gt_of_ne hp with h | h
    · simp [U, L, h, not_lt.mpr h.le]
    · simp [U, L, h, not_lt.mpr h.le])
  calc
    _ = ∫ p, U p + L p ∂ν.prod ν := integral_congr_ae he
    _ = (∫ p, U p ∂ν.prod ν) + ∫ p, L p ∂ν.prod ν := integral_add hu hl
    _ = _ := congrArg (fun z => orderedTimeIntegral ν H + z)
      (integral_prod_swap L).symm

end TimeTraps.Probability
