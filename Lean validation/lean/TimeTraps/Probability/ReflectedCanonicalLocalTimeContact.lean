module

public import TimeTraps.Probability.ReflectedCanonicalLocalTime

@[expose] public section

/-! The canonical additive functional has the exact original reflected
local-time increments and an atomless measure supported on actual
particle contacts. No contact-measure identity is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal ENNReal

theorem reflectedCanonicalLocalTime_contact (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      ∃ h : HasContinuousOccupationLocalTime a.val (fun r => 2 * r) (reflectedCanonicalPath L hL D x ω),
        let ν := continuousPathLocalTimeMeasure h (fun r hr => by positivity)
        ν.support ⊆ {t : ℝ | 0 ≤ t ∧ foldedTrajectory L D x brownianDyadicPath t.toNNReal ω = a.val} ∧
          (∀ s t : ℝ≥0, ν (Ioc s.val t.val) =
            ENNReal.ofReal (reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω -
              reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val s ω)) ∧
          ∀ t : ℝ, ν {t} = 0 := by
  filter_upwards [reflectedCanonicalLocalTime_identification L hL D hD x a,
    reflectedCanonicalPath_actual_ae L hL D x] with ω hi hp
  refine ⟨hi.1, ?_, ?_, fun t => continuousPathLocalTimeMeasure_singleton hi.1 _ t⟩
  · intro t ht
    obtain ⟨ht0, he⟩ := continuousPathLocalTimeMeasure_support hi.1 (fun r hr => by positivity) ht
    exact ⟨ht0, (hp t.toNNReal).symm.trans he⟩
  · intro s t
    rw [continuousPathLocalTimeMeasure_Ioc]
    have he (r : ℝ≥0) : continuousPathLocalTime a.val (fun h => 2 * h)
        (reflectedCanonicalPath L hL D x ω) r =
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val r ω :=
      (hi.1.value_eq r).symm.trans (hi.2 r)
    rw [he s, he t]

end TimeTraps.Probability

end
