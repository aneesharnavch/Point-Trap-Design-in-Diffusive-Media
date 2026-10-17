module

public import TimeTraps.Probability.ReversibleResistanceCanonicalLocalTimeData
public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousHorizons
public import TimeTraps.Probability.ContinuousPathLocalTimeSupport

@[expose] public section

/-! The original physical fixed-site local time is the canonical
positive continuous additive functional of the actual particle path.
One event gives the identification and the cocycle at every pair of times;
the normalization is the original physical speed-measure band mass. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceCanonicalLocalTime_identification (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      HasContinuousOccupationLocalTime a (resistancePhysicalBandMass A a)
        (reversibleResistanceCanonicalPath A x ω) ∧
          ∀ t : ℝ≥0, reversibleResistanceCanonicalLocalTime A x a t ω =
            reversibleResistanceLocalTime A x a t ω := by
  have hb : ∀ᵐ ω ∂brownianCompletedMeasure, ∀ N : ℕ,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |reversibleResistancePhysicalOccupationBand A x a h t.val ω -
          reversibleResistanceLocalTime A x a t.val ω|) (𝓝[>] 0) (𝓝 0) :=
    reversibleResistancePhysicalBand_all_natural_horizons_as A x ha
  have hc : ∀ᵐ ω ∂brownianCompletedMeasure,
      Continuous (fun t => reversibleResistanceLocalTime A x a t ω) :=
    (reversibleResistanceLocalTime_paths A x a).mono (fun _ h => h.1)
  filter_upwards [hb, hc] with ω hb hc
  let l : ReversibleNeumannFullPath := ⟨fun t => reversibleResistanceLocalTime A x a t ω, hc⟩
  have hsup (N : ℕ) : Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
      |continuousPathOccupationBand a h (resistancePhysicalBandMass A a h)
        (reversibleResistanceCanonicalPath A x ω) t.val - l t.val|) (𝓝[>] 0) (𝓝 0) := by
    have he : (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |continuousPathOccupationBand a h (resistancePhysicalBandMass A a h)
          (reversibleResistanceCanonicalPath A x ω) t.val - l t.val|) =
        (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
          |reversibleResistancePhysicalOccupationBand A x a h t.val ω -
            reversibleResistanceLocalTime A x a t.val ω|) := by
      funext h
      congr 1
    rw [he]
    exact hb N
  obtain ⟨hg, he⟩ := hasContinuousOccupationLocalTime_of_natural_sup a (resistancePhysicalBandMass A a)
    (reversibleResistanceCanonicalPath A x ω) l hsup
  exact ⟨hg, fun t => (hg.value_eq t).trans (congrArg (fun q : ReversibleNeumannFullPath => q t) he)⟩

theorem reversibleResistanceCanonicalLocalTime_cocycle (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ s t : ℝ≥0,
      reversibleResistanceLocalTime A x a (s + t) ω = reversibleResistanceLocalTime A x a s ω +
        continuousPathLocalTimeValue a (resistancePhysicalBandMass A a) t
          (continuousPathShift s (reversibleResistanceCanonicalPath A x ω)) := by
  filter_upwards [reversibleResistanceCanonicalLocalTime_identification A x ha] with ω hω s t
  have he := hω.1.value_cocycle s t
  change reversibleResistanceCanonicalLocalTime A x a (s + t) ω =
    reversibleResistanceCanonicalLocalTime A x a s ω + _ at he
  simpa only [hω.2] using he

theorem reversibleResistanceCanonicalLocalTime_good_path_law (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ p ∂brownianCompletedMeasure.map (reversibleResistanceCanonicalPath A x),
      HasContinuousOccupationLocalTime a (resistancePhysicalBandMass A a) p := by
  apply (ae_map_iff (reversibleResistanceCanonicalPath_measurable A x).aemeasurable
    (hasContinuousOccupationLocalTime_measurableSet a (resistancePhysicalBandMass A a))).mpr
  exact (reversibleResistanceCanonicalLocalTime_identification A x ha).mono (fun _ h => h.1)

theorem reversibleResistanceCanonicalLocalTime_paths (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      Continuous (fun t => reversibleResistanceCanonicalLocalTime A x a t ω) ∧
        Monotone (fun t => reversibleResistanceCanonicalLocalTime A x a t ω) ∧
          reversibleResistanceCanonicalLocalTime A x a 0 ω = 0 := by
  filter_upwards [reversibleResistanceCanonicalLocalTime_identification A x ha] with ω hω
  have he : (fun t => reversibleResistanceCanonicalLocalTime A x a t ω) =
      continuousPathLocalTime a (resistancePhysicalBandMass A a) (reversibleResistanceCanonicalPath A x ω) :=
    funext hω.1.value_eq
  rw [he]
  exact ⟨(continuousPathLocalTime _ _ _).continuous,
    hω.1.monotone (fun r hr => (resistancePhysicalBandMass_pos A a hr).le),
      (hω.1.value_eq 0).trans hω.1.zero⟩

end TimeTraps.Probability

end
