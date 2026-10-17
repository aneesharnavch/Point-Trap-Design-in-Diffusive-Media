module

public import TimeTraps.Probability.ReflectedInteriorOccupationMeasurable

@[expose] public section

/-! The actual interior coefficient, extended by zero at both endpoints
and outside the interval, is a jointly measurable occupation density.
Fubini gives spatial almost-everywhere identification on one event at
each fixed horizon. No simultaneous pointwise assertion at all levels
or common event over all horizons is used. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def reflectedInteriorOccupationDensity (L D x : ℝ) (T : ℝ≥0)
    (ω : ℕ → ℝ) (a : ℝ) : ℝ :=
  (Ioo 0 L).indicator
    (fun a => reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω) a

theorem reflectedInteriorOccupationDensity_jointlyMeasurable
    (L D x : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedInteriorOccupationDensity L D x T p.2 p.1) := by
  let A : Set (ℝ × (ℕ → ℝ)) := {p | p.1 ∈ Ioo 0 L}
  have hA : MeasurableSet A := measurableSet_Ioo.preimage measurable_fst
  exact (reflectedInteriorOccupationCoefficient_jointlyMeasurable
    x (Real.sqrt (2 * D)) L T).indicator hA

theorem reflectedInteriorOccupationDensity_spatial_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      reflectedInteriorOccupationDensity L D x T ω =ᵐ[volume]
        foldedOccupationDensity L D x T ω := by
  have hlevel : ∀ a : ℝ, ∀ᵐ ω ∂brownianDyadicMeasure,
      reflectedInteriorOccupationDensity L D x T ω a =
        foldedOccupationDensity L D x T ω a := by
    intro a
    by_cases ha : a ∈ Ioo 0 L
    · filter_upwards [reflectedInteriorOccupationCoefficient_density_all_times_ae
        L hL D hD x a ha] with ω hω
      simpa only [reflectedInteriorOccupationDensity, indicator_of_mem ha] using hω T
    · exact Filter.Eventually.of_forall (fun ω => by
        simp only [reflectedInteriorOccupationDensity, foldedOccupationDensity,
          foldedOccupationDensityENNReal, indicator_of_notMem ha, ENNReal.toReal_zero])
  have hm : MeasurableSet {p : ℝ × (ℕ → ℝ) |
      reflectedInteriorOccupationDensity L D x T p.2 p.1 =
        foldedOccupationDensity L D x T p.2 p.1} :=
    measurableSet_eq_fun (reflectedInteriorOccupationDensity_jointlyMeasurable L D x T)
      (foldedOccupationDensity_timeSlice_jointlyMeasurable L D x T)
  exact (Measure.ae_ae_comm hm).mp (Filter.Eventually.of_forall hlevel)

end TimeTraps.Probability

end
