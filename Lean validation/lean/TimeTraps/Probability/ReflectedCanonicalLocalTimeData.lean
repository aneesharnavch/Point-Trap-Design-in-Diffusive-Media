module

public import TimeTraps.Probability.ContinuousPathLocalTimeAdapted
public import TimeTraps.Probability.ContinuousPathLocalTimeCompact
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentBandHorizons

@[expose] public section

/-! The actual reflected process is realized in the canonical continuous
path space. Its literal ordinary occupation bands agree with the generic
bands, with exactly the reference normalization 2h. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def reflectedCanonicalPath (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (ω : BrownianCompletedSample) : ReversibleNeumannFullPath :=
  ⟨fun t => (reflectedMarkovState L hL D x t ω).val,
    (reflectedMarkovState_continuous L hL D x ω).subtype_val⟩

theorem reflectedCanonicalPath_stronglyAdapted (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    StronglyAdapted brownianCompletedFiltration.rightCont
      (fun t ω => reflectedCanonicalPath L hL D x ω t) := by
  intro t
  exact continuous_subtype_val.comp_stronglyMeasurable (reflectedMarkovState_stronglyAdapted L hL D x t)

theorem reflectedCanonicalPath_measurable (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    Measurable (reflectedCanonicalPath L hL D x) := by
  apply reversibleNeumannFullPathSample_measurableEmbedding.measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun n =>
    ((reflectedCanonicalPath_stronglyAdapted L hL D x (denseSeq ℝ≥0 n)).mono
      (brownianCompletedFiltration.rightCont.le _)).measurable)

theorem reflectedCanonicalPath_actual_ae (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t : ℝ≥0,
      reflectedCanonicalPath L hL D x ω t = foldedTrajectory L D x brownianDyadicPath t ω :=
  reflectedMarkovState_actual_ae L hL D x

theorem continuousPathOccupationBand_eq_reflected (L D x a h : ℝ)
    (p : ReversibleNeumannFullPath) (ω : ℕ → ℝ)
    (hp : ∀ t, p t = foldedTrajectory L D x brownianDyadicPath t ω) (t : ℝ≥0) :
    continuousPathOccupationBand a h (2 * h) p t = reflectedOccupationBand L D x a h t ω := by
  change (∫ r in (0 : ℝ)..t.val, brownianBandIndicator a h (p r.toNNReal)) / (2 * h) =
    (1 / (2 * h)) * ∫ r in (0 : ℝ)..t.val,
      brownianBandIndicator a h (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
  have he : (∫ r in (0 : ℝ)..t.val, brownianBandIndicator a h (p r.toNNReal)) =
      ∫ r in (0 : ℝ)..t.val,
        brownianBandIndicator a h (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) := by
    apply intervalIntegral.integral_congr
    intro r _
    exact congrArg (brownianBandIndicator a h) (hp r.toNNReal)
  rw [he]
  ring

def reflectedCanonicalLocalTime (L : ℝ) (hL : 0 < L) (D x a : ℝ)
    (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  continuousPathLocalTimeValue a (fun h => 2 * h) t (reflectedCanonicalPath L hL D x ω)

theorem reflectedCanonicalLocalTime_stronglyAdapted (L : ℝ) (hL : 0 < L) (D x a : ℝ) :
    StronglyAdapted brownianCompletedFiltration.rightCont (reflectedCanonicalLocalTime L hL D x a) :=
  continuousPathLocalTimeValue_stronglyAdapted _ _
    (reflectedCanonicalPath_stronglyAdapted L hL D x) a (fun h => 2 * h)

end TimeTraps.Probability

end
