module

public import TimeTraps.Probability.KillingLifetimeMeanMeasurable
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

/-! Layer cake for extended nonnegative values, including infinity.
The formula follows from the length of an interval and Tonelli, rather
than reducing to a finite-valued or integrable lifetime. -/

namespace TimeTraps.Probability

open Set MeasureTheory
open scoped ENNReal

theorem extendedLifetime_layercake_point (x : ℝ≥0∞) :
    x = ∫⁻ t in Ioi (0 : ℝ), {s : ℝ | ENNReal.ofReal s < x}.indicator (fun _ => (1 : ℝ≥0∞)) t := by
  classical
  induction x using ENNReal.recTopCoe with
  | top => simp [Real.volume_Ioi]
  | coe r =>
    have hs : Iio (r : ℝ) ∩ Ioi (0 : ℝ) = Ioo 0 (r : ℝ) := by
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
    calc
      (r : ℝ≥0∞) = volume (Ioo (0 : ℝ) (r : ℝ)) := by
        rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_coe_nnreal]
      _ = ∫⁻ t in Ioi (0 : ℝ), (Iio (r : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) t := by
        rw [setLIntegral_indicator measurableSet_Iio, lintegral_one,
          Measure.restrict_apply MeasurableSet.univ, univ_inter, hs]
      _ = _ := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [indicator_apply, mem_ofPred_eq, mem_Iio, ENNReal.ofReal_lt_coe_iff ht.le]

theorem extendedLifetime_layercake {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ≥0∞) (hf : AEMeasurable f μ) :
    (∫⁻ ω, f ω ∂μ) = ∫⁻ t in Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < f ω} := by
  classical
  have hm : AEMeasurable
      (Function.uncurry (fun ω t => {s : ℝ | ENNReal.ofReal s < f ω}.indicator (fun _ => (1 : ℝ≥0∞)) t))
      (μ.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hs : NullMeasurableSet {p : α × ℝ | ENNReal.ofReal p.2 < f p.1}
        (μ.prod (volume.restrict (Ioi (0 : ℝ)))) :=
      nullMeasurableSet_lt (by fun_prop) hf.comp_fst
    exact (aemeasurable_const : AEMeasurable (fun _ : α × ℝ => (1 : ℝ≥0∞))
      (μ.prod (volume.restrict (Ioi (0 : ℝ))))).indicator₀ hs
  calc
    _ = ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ),
        {s : ℝ | ENNReal.ofReal s < f ω}.indicator (fun _ => (1 : ℝ≥0∞)) t) ∂μ :=
      lintegral_congr (fun ω => extendedLifetime_layercake_point (f ω))
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω,
        {s : ℝ | ENNReal.ofReal s < f ω}.indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ :=
      lintegral_lintegral_swap hm
    _ = _ := by
      apply lintegral_congr
      intro t
      have he : (fun ω => {s : ℝ | ENNReal.ofReal s < f ω}.indicator (fun _ => (1 : ℝ≥0∞)) t) =
          {ω | ENNReal.ofReal t < f ω}.indicator (fun _ => (1 : ℝ≥0∞)) := rfl
      rw [he, lintegral_indicator₀ (nullMeasurableSet_lt aemeasurable_const hf), lintegral_one,
        Measure.restrict_apply MeasurableSet.univ, univ_inter]

theorem contactLifetime_layercake {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable (A t))
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    (∫⁻ p, contactLifetimeValue A p ∂exponentialKillingMeasure μ) =
      ∫⁻ t in Ioi (0 : ℝ), exponentialKillingMeasure μ
        {p : Ω × ℝ | (t : WithTop ℝ) < contactLifetime A p} := by
  let _ := exponentialKilling_probability μ
  rw [extendedLifetime_layercake (exponentialKillingMeasure μ) (contactLifetimeValue A)
    (contactLifetimeValue_aemeasurable μ A hA hc hm)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  apply congrArg (exponentialKillingMeasure μ)
  ext p
  exact nonnegativeLifetimeValue_lt_iff t ht.le (contactLifetime A p)

end TimeTraps.Probability
