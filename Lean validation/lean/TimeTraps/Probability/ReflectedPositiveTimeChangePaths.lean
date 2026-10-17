module

public import TimeTraps.Probability.ReflectedPositiveTimeChange
public import TimeTraps.Probability.BrownianDenseContinuityPath

@[expose] public section

/-! On the actual Brownian continuity event, the literal reflected clock
and inverse have their path properties simultaneously at every time.
The spatial speed is only continuous and positive on the compact interval.
No optional-sampling or diffusion identification is used. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem reflectedPositiveTimeChange_regular_ae (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun s => reflectedPositiveTimeClock L D x brownianDyadicPath c s ω) ∧
      StrictMono (fun s => reflectedPositiveTimeClock L D x brownianDyadicPath c s ω) ∧
      Tendsto (fun s => reflectedPositiveTimeClock L D x brownianDyadicPath c s ω) atTop atTop ∧
      Continuous (fun t => reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ∧
      StrictMono (fun t => reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ∧
      ∀ t, reflectedPositiveTimeClock L D x brownianDyadicPath c
          (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω = t ∧
        reflectedPositiveTimeInverse L D x brownianDyadicPath c
          (reflectedPositiveTimeClock L D x brownianDyadicPath c t ω) ω = t := by
  filter_upwards [brownianDyadicPath_continuous_ae] with ω hω
  exact reflectedPositiveTimeChange_regular L hL D x brownianDyadicPath c hc hpos ω hω

theorem reflectedPositiveTimeChange_bounds_ae (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    ∃ m M : ℝ≥0, 0 < m ∧
      (∃ y ∈ Icc 0 L, c y = (m : ℝ) ∧ ∀ z ∈ Icc 0 L, c y ≤ c z) ∧
      (∃ y ∈ Icc 0 L, c y = (M : ℝ) ∧ ∀ z ∈ Icc 0 L, c z ≤ c y) ∧
      ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t,
        m * t ≤ reflectedPositiveTimeClock L D x brownianDyadicPath c t ω ∧
        reflectedPositiveTimeClock L D x brownianDyadicPath c t ω ≤ M * t ∧
        t / M ≤ reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω ∧
        reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω ≤ t / m := by
  obtain ⟨ymin, hymin, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  obtain ⟨ymax, hymax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c ymin, (hpos ymin hymin).le⟩
  let M : ℝ≥0 := ⟨c ymax, (hpos ymax hymax).le⟩
  refine ⟨m, M, hpos ymin hymin, ⟨ymin, hymin, rfl, fun _ hz => hmin hz⟩,
    ⟨ymax, hymax, rfl, fun _ hz => hmax hz⟩, ?_⟩
  filter_upwards [brownianDyadicPath_continuous_ae] with ω hω
  let v := reflectedPositiveTimeSpeed L hL D x brownianDyadicPath c hc hpos ω hω
  obtain ⟨⟨u, hu, hemin, hule⟩, ⟨z, hz, hemax, hlez⟩⟩ :=
    reflectedPositiveTimeSpeed_extrema L hL D x brownianDyadicPath c hc hpos ω hω
  have hm : v.lower = m := by
    apply NNReal.eq
    change (v.lower : ℝ) = c ymin
    rw [← hemin]
    exact le_antisymm (hule ymin hymin) (hmin hu)
  have hM : v.upper = M := by
    apply NNReal.eq
    change (v.upper : ℝ) = c ymax
    rw [← hemax]
    exact le_antisymm (hmax hz) (hlez ymax hymax)
  intro t
  have hb := reflectedPositiveTimeChange_bounds L hL D x brownianDyadicPath c hc hpos ω hω t
  change v.lower * t ≤ reflectedPositiveTimeClock L D x brownianDyadicPath c t ω ∧
    reflectedPositiveTimeClock L D x brownianDyadicPath c t ω ≤ v.upper * t ∧
    t / v.upper ≤ reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω ∧
    reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω ≤ t / v.lower at hb
  rwa [hm, hM] at hb

end TimeTraps.Probability
