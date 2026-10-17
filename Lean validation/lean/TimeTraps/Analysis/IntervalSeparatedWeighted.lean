module

public import TimeTraps.Analysis.IntervalSeparatedDense
public import TimeTraps.Analysis.IntervalSeparatedPhysical
public import TimeTraps.Analysis.IntervalWeightedState

@[expose] public section

/-! Compact dense speed-weighted inclusion for every separated endpoint
selection, including unrestricted values at both endpoints. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {l r : ℝ}

noncomputable def IntervalSeparatedBoundary.weightedStateL (B : IntervalSeparatedBoundary l r)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc l r)) :
    IntervalSeparatedSpace B →L[ℝ] IntervalSobolevL2 l r :=
  (intervalWeightedStateL w hw).comp B.subspace.subtypeL

theorem IntervalSeparatedBoundary.weightedStateL_inner (B : IntervalSeparatedBoundary l r)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 ≤ w x)
    (u v : IntervalSeparatedSpace B) :
    inner ℝ (B.weightedStateL w hw u) (B.weightedStateL w hw v) =
      ∫ x in l..r, w x * u.val.representative B.interval_pos x *
        v.val.representative B.interval_pos x :=
  intervalWeightedStateL_inner B.interval_pos w hw hp u.val v.val

theorem IntervalSeparatedBoundary.weightedStateL_injective (B : IntervalSeparatedBoundary l r)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 < w x) :
    Function.Injective (B.weightedStateL w hw) :=
  (intervalWeightedStateL_injective w hw hp).comp Subtype.val_injective

theorem IntervalSeparatedBoundary.weightedStateL_compact (B : IntervalSeparatedBoundary l r)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc l r)) :
    IsCompactOperator (B.weightedStateL w hw) :=
  (intervalWeightedStateL_compact B.interval_pos w hw).comp_clm B.subspace.subtypeL

theorem IntervalSeparatedBoundary.weightedStateL_denseRange (B : IntervalSeparatedBoundary l r)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 < w x) :
    DenseRange (B.weightedStateL w hw) := by
  exact ((intervalContinuousMultiplyL_bijective (fun x => Real.sqrt (w x)) hw.sqrt
    (fun x hx => (Real.sqrt_pos.2 (hp x hx)).ne')).2.denseRange).comp
      B.stateL_denseRange
      (intervalContinuousMultiplyL (fun x => Real.sqrt (w x)) hw.sqrt).continuous

end TimeTraps.Analysis
