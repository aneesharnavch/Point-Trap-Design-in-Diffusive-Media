module

public import TimeTraps.Probability.BoundedContinuousLaplaceMeasure
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! A nonnegative bounded continuous function on time defines a genuine
finite discounted measure. Mapping it to nonnegative time retains exactly
the positive-time density and shifts its Laplace transform by one. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

def discountedTimeDensity (u : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-t) * u t)

def discountedTimeMeasure (u : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (discountedTimeDensity u)

def discountedNonnegativeTimeMeasure (u : ℝ → ℝ) : Measure ℝ≥0 :=
  (discountedTimeMeasure u).map Real.toNNReal

theorem discountedTimeDensity_measurable {u : ℝ → ℝ} (hu : Continuous u) :
    Measurable (discountedTimeDensity u) := by
  unfold discountedTimeDensity
  fun_prop

theorem discountedTimeMeasure_finite {u : ℝ → ℝ} (hu : Continuous u)
    (hpos : ∀ t, 0 ≤ u t) {M : ℝ} (hb : ∀ t, ‖u t‖ ≤ M) :
    IsFiniteMeasure (discountedTimeMeasure u) := by
  have hi : IntegrableOn (fun t => Real.exp (-t) * u t) (Ioi (0 : ℝ)) := by
    simpa only [neg_one_mul] using boundedDynkin_discounted_integrable hu hb (show (0 : ℝ) < 1 by norm_num)
  exact isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun t =>
      mul_nonneg (Real.exp_pos _).le (hpos t)))).mp hi.hasFiniteIntegral).ne

theorem discountedNonnegativeTimeMeasure_finite {u : ℝ → ℝ} (hu : Continuous u)
    (hpos : ∀ t, 0 ≤ u t) {M : ℝ} (hb : ∀ t, ‖u t‖ ≤ M) :
    IsFiniteMeasure (discountedNonnegativeTimeMeasure u) := by
  let := discountedTimeMeasure_finite hu hpos hb
  unfold discountedNonnegativeTimeMeasure
  infer_instance

theorem discountedNonnegativeTimeMeasure_map_coe (u : ℝ → ℝ) :
    (discountedNonnegativeTimeMeasure u).map (fun t : ℝ≥0 => (t : ℝ)) = discountedTimeMeasure u := by
  rw [discountedNonnegativeTimeMeasure, Measure.map_map NNReal.continuous_coe.measurable
    continuous_real_toNNReal.measurable]
  calc
    _ = (discountedTimeMeasure u).map id := by
      apply Measure.map_congr
      apply withDensity_absolutelyContinuous
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.coe_toNNReal t ht.le
    _ = _ := Measure.map_id

theorem discountedNonnegativeTimeMeasure_laplace {u : ℝ → ℝ} (hu : Continuous u)
    (hpos : ∀ t, 0 ≤ u t) (a : ℝ≥0) :
    (∫ t, Real.exp (-(a : ℝ) * (t : ℝ)) ∂discountedNonnegativeTimeMeasure u) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-((a : ℝ) + 1) * t) * u t := by
  rw [discountedNonnegativeTimeMeasure,
    integral_map continuous_real_toNNReal.measurable.aemeasurable
      (show AEStronglyMeasurable (fun t : ℝ≥0 => Real.exp (-(a : ℝ) * (t : ℝ)))
        ((discountedTimeMeasure u).map Real.toNNReal) from
        (show Continuous (fun t : ℝ≥0 => Real.exp (-(a : ℝ) * (t : ℝ))) by fun_prop).aestronglyMeasurable),
    discountedTimeMeasure, integral_withDensity_eq_integral_toReal_smul
      (discountedTimeDensity_measurable hu)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (ENNReal.ofReal (Real.exp (-t) * u t)).toReal *
    Real.exp (-(a : ℝ) * (t.toNNReal : ℝ)) = _
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (hpos t)), Real.coe_toNNReal t ht.le]
  calc
    _ = (Real.exp (-t) * Real.exp (-(a : ℝ) * t)) * u t := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end TimeTraps.Probability

end
