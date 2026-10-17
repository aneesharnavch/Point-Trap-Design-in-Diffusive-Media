module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

/-! Ordinary real indicator integrals determine the values of a
nonnegative density measure and of a finite pushforward measure. -/

namespace TimeTraps.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

theorem withDensity_ofReal_apply_indicator {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {s : Set ℝ} (hs : MeasurableSet s)
    (hi : Integrable (fun x => s.indicator (fun _ => (1 : ℝ)) x * w x) volume) :
    volume.withDensity (fun x => ENNReal.ofReal (w x)) s =
      ENNReal.ofReal (∫ x, s.indicator (fun _ => (1 : ℝ)) x * w x) := by
  have he : (fun x => s.indicator (fun _ => (1 : ℝ)) x * w x) = s.indicator w := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [he] at hi ⊢
  rw [withDensity_apply _ hs, integral_indicator hs]
  exact (ofReal_integral_eq_lintegral_ofReal ((integrable_indicator_iff hs).mp hi)
    (Eventually.of_forall hw)).symm

theorem finite_map_apply_ofReal_indicator {A : Type*} [MeasurableSpace A]
    {ν : Measure A} [IsFiniteMeasure ν] {X : A → ℝ} (hX : Measurable X)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ν.map X s = ENNReal.ofReal (∫ x, s.indicator (fun _ => (1 : ℝ)) (X x) ∂ν) := by
  have he : (∫ x, s.indicator (fun _ => (1 : ℝ)) (X x) ∂ν) = (ν.map X).real s := by
    rw [← integral_map hX.aemeasurable ((measurable_const.indicator hs).aestronglyMeasurable)]
    exact integral_indicator_one hs
  rw [he]
  exact (ENNReal.ofReal_toReal (measure_ne_top (ν.map X) s)).symm

end TimeTraps.Analysis
