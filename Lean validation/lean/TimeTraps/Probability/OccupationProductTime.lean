module

public import TimeTraps.Probability.OccupationProductFubini
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Finite-horizon occupation products and chronological replacement on
the strict time triangle. Values off the true time domain and on the
diagonal are irrelevant by proved measure statements. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω]

theorem timePair_Ioc_mem_ae (T : ℝ) :
    ∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)),
      p.1 ∈ Ioc 0 T ∧ p.2 ∈ Ioc 0 T := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (ae_restrict_mem measurableSet_Ioc).mono (fun _ ht => ⟨hs, ht⟩)

theorem orderedTimeIntegrand_Ioc_congr (T : ℝ) (H J : ℝ × ℝ → ℝ)
    (he : ∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s < t → H (s, t) = J (s, t)) :
    (fun p => if p.1 < p.2 then H p else 0) =ᵐ[
      (volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))]
        (fun p => if p.1 < p.2 then J p else 0) := by
  filter_upwards [timePair_Ioc_mem_ae T] with p hp
  by_cases h : p.1 < p.2
  · simp only [if_pos h]
    exact he p.1 hp.1 p.2 hp.2 h
  · simp only [if_neg h]

theorem orderedTimeIntegrand_Ioc_integrable (T : ℝ) (H J : ℝ × ℝ → ℝ)
    (hH : Integrable H ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))))
    (he : ∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s < t → H (s, t) = J (s, t)) :
    Integrable (fun p => if p.1 < p.2 then J p else 0)
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))) :=
  (hH.indicator (measurableSet_lt measurable_fst measurable_snd)).congr
    (orderedTimeIntegrand_Ioc_congr T H J he)

theorem occupationProduct_interval_ordered (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℝ → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {B C : ℝ} (hB : ∀ s ω, ‖F s ω‖ ≤ B) (hC : ∀ s ω, ‖G s ω‖ ≤ C)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, (∫ s in 0..T, F s ω) * (∫ t in 0..T, G t ω) ∂μ) =
      orderedTimeIntegral (volume.restrict (Ioc 0 T)) (fun p => ∫ ω, F p.1 ω * G p.2 ω ∂μ) +
      orderedTimeIntegral (volume.restrict (Ioc 0 T)) (fun p => ∫ ω, G p.1 ω * F p.2 ω ∂μ) := by
  simp_rw [intervalIntegral.integral_of_le hT]
  exact occupationProduct_expectation_ordered μ (volume.restrict (Ioc 0 T)) F G hF hG hB hC

end TimeTraps.Probability
