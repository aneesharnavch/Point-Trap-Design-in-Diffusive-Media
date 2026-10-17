module

public import TimeTraps.Probability.ContinuousPathLocalTimeAdapted
public import TimeTraps.Probability.ContinuousPathLocalTimeCompact
public import TimeTraps.Probability.ReversibleResistancePhysicalBandData
public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimePaths

@[expose] public section

/-! The actual variable-coefficient physical process in canonical path
space. The canonical band denominator is the original speed-measure
mass of the physical band, with no conductance factor added. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace TimeTraps.Interval
open scoped NNReal ENNReal Topology

def reversibleResistanceCanonicalPath (A : IntervalMedium) (x : ℝ)
    (ω : BrownianCompletedSample) : ReversibleNeumannFullPath :=
  ⟨fun t => reversibleResistancePath A x t ω, reversibleResistancePath_continuous A x ω⟩

theorem reversibleResistanceCanonicalPath_stronglyAdapted (A : IntervalMedium) (x : ℝ) :
    StronglyAdapted (reversibleResistanceFiltration A x)
      (fun t ω => reversibleResistanceCanonicalPath A x ω t) :=
  fun t => reversibleResistancePath_borel_stronglyMeasurable A x t measurable_id

theorem reversibleResistanceCanonicalPath_measurable (A : IntervalMedium) (x : ℝ) :
    Measurable (reversibleResistanceCanonicalPath A x) := by
  apply reversibleNeumannFullPathSample_measurableEmbedding.measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun n =>
    ((reversibleResistanceCanonicalPath_stronglyAdapted A x (denseSeq ℝ≥0 n)).mono
      ((reversibleResistanceFiltration A x).le _)).measurable)

theorem reversibleResistanceCanonicalPath_band (A : IntervalMedium) (x a h : ℝ)
    (t : ℝ≥0) (ω : BrownianCompletedSample) :
    continuousPathOccupationBand a h (resistancePhysicalBandMass A a h)
      (reversibleResistanceCanonicalPath A x ω) t =
        reversibleResistancePhysicalOccupationBand A x a h t ω := rfl

def reversibleResistanceCanonicalLocalTime (A : IntervalMedium) (x a : ℝ)
    (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  continuousPathLocalTimeValue a (resistancePhysicalBandMass A a) t
    (reversibleResistanceCanonicalPath A x ω)

theorem reversibleResistanceCanonicalLocalTime_stronglyAdapted (A : IntervalMedium) (x a : ℝ) :
    StronglyAdapted (reversibleResistanceFiltration A x) (reversibleResistanceCanonicalLocalTime A x a) :=
  continuousPathLocalTimeValue_stronglyAdapted _ _
    (reversibleResistanceCanonicalPath_stronglyAdapted A x) a (resistancePhysicalBandMass A a)

theorem reversibleResistanceCanonicalLocalTime_jointlyMeasurable (A : IntervalMedium) (x a : ℝ) :
    Measurable (fun q : ℝ≥0 × BrownianCompletedSample => reversibleResistanceCanonicalLocalTime A x a q.1 q.2) := by
  let f : ℝ≥0 × BrownianCompletedSample → ℝ≥0 × ReversibleNeumannFullPath :=
    fun q => (q.1, reversibleResistanceCanonicalPath A x q.2)
  have hf : Measurable f := measurable_fst.prodMk
    ((reversibleResistanceCanonicalPath_measurable A x).comp measurable_snd)
  have hm := (continuousPathLocalTimeValue_jointlyMeasurable a (resistancePhysicalBandMass A a)).comp hf
  have he : (fun q : ℝ≥0 × BrownianCompletedSample => reversibleResistanceCanonicalLocalTime A x a q.1 q.2) =
      (fun q : ℝ≥0 × ReversibleNeumannFullPath =>
        continuousPathLocalTimeValue a (resistancePhysicalBandMass A a) q.1 q.2) ∘ f := by
    funext q
    rfl
  exact he.symm ▸ hm

end TimeTraps.Probability

end
