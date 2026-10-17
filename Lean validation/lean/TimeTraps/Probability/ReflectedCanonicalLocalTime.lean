module

public import TimeTraps.Probability.ReflectedCanonicalLocalTimeData
public import TimeTraps.Probability.ContinuousPathLocalTimeSupport

@[expose] public section

/-! Almost every actual reflected path belongs to the canonical,
shift-invariant local-time good set. Its canonical additive functional
equals the original fixed-site coefficient simultaneously at every time.
The proof uses the full positive-radius compact-time band limit. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem reflectedCanonicalLocalTime_identification (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      HasContinuousOccupationLocalTime a.val (fun h => 2 * h) (reflectedCanonicalPath L hL D x ω) ∧
        ∀ t : ℝ≥0, reflectedCanonicalLocalTime L hL D x a.val t ω =
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω := by
  have hb : ∀ᵐ ω ∂brownianCompletedMeasure, ∀ N : ℕ,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |reflectedOccupationBand L D x a.val h t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|)
        (𝓝[>] 0) (𝓝 0) := reflectedOccupationBand_all_natural_horizons_as L hL D hD x a
  have hr : ∀ᵐ ω ∂brownianCompletedMeasure,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a.val ω :=
    reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a.val
  filter_upwards [hb, hr, reflectedCanonicalPath_actual_ae L hL D x] with ω hb hr hp
  let l : ReversibleNeumannFullPath :=
    ⟨fun t => reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω,
      (reflectedInteriorCorrection_continuous (Real.sqrt_pos.mpr (by positivity)) hL hr).div_const _⟩
  have hsup (N : ℕ) : Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
      |continuousPathOccupationBand a.val h (2 * h) (reflectedCanonicalPath L hL D x ω) t.val - l t.val|)
      (𝓝[>] 0) (𝓝 0) := by
    have he : (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |continuousPathOccupationBand a.val h (2 * h) (reflectedCanonicalPath L hL D x ω) t.val - l t.val|) =
        (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
          |reflectedOccupationBand L D x a.val h t.val ω -
            reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|) := by
      funext h
      congr 1
      funext t
      change |continuousPathOccupationBand a.val h (2 * h) (reflectedCanonicalPath L hL D x ω) t.val -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω| = _
      rw [continuousPathOccupationBand_eq_reflected L D x a.val h _ ω hp]
    rw [he]
    exact hb N
  obtain ⟨hg, he⟩ := hasContinuousOccupationLocalTime_of_natural_sup a.val (fun h => 2 * h)
    (reflectedCanonicalPath L hL D x ω) l hsup
  refine ⟨hg, fun t => ?_⟩
  exact (hg.value_eq t).trans (congrArg (fun q : ReversibleNeumannFullPath => q t) he)

theorem reflectedCanonicalLocalTime_cocycle (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ s t : ℝ≥0,
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val (s + t) ω =
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val s ω +
          continuousPathLocalTimeValue a.val (fun h => 2 * h) t
            (continuousPathShift s (reflectedCanonicalPath L hL D x ω)) := by
  filter_upwards [reflectedCanonicalLocalTime_identification L hL D hD x a] with ω hω s t
  have he := hω.1.value_cocycle s t
  change reflectedCanonicalLocalTime L hL D x a.val (s + t) ω =
    reflectedCanonicalLocalTime L hL D x a.val s ω + _ at he
  simpa only [hω.2] using he

theorem reflectedCanonicalLocalTime_good_path_law (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ p ∂brownianCompletedMeasure.map (reflectedCanonicalPath L hL D x),
      HasContinuousOccupationLocalTime a.val (fun h => 2 * h) p := by
  apply (ae_map_iff (reflectedCanonicalPath_measurable L hL D x).aemeasurable
    (hasContinuousOccupationLocalTime_measurableSet a.val (fun h => 2 * h))).mpr
  exact (reflectedCanonicalLocalTime_identification L hL D hD x a).mono (fun _ h => h.1)

theorem reflectedCanonicalLocalTime_paths (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      Continuous (fun t => reflectedCanonicalLocalTime L hL D x a.val t ω) ∧
        Monotone (fun t => reflectedCanonicalLocalTime L hL D x a.val t ω) ∧
          reflectedCanonicalLocalTime L hL D x a.val 0 ω = 0 := by
  filter_upwards [reflectedCanonicalLocalTime_identification L hL D hD x a] with ω hω
  have he : (fun t => reflectedCanonicalLocalTime L hL D x a.val t ω) =
      continuousPathLocalTime a.val (fun h => 2 * h) (reflectedCanonicalPath L hL D x ω) :=
    funext hω.1.value_eq
  rw [he]
  exact ⟨(continuousPathLocalTime _ _ _).continuous, hω.1.monotone (fun r hr => by positivity),
    (hω.1.value_eq 0).trans hω.1.zero⟩

end TimeTraps.Probability

end
