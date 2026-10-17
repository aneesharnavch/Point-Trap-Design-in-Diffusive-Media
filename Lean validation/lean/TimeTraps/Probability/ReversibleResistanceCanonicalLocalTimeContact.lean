module

public import TimeTraps.Probability.ReversibleResistanceCanonicalLocalTime
public import TimeTraps.Probability.ReflectedCanonicalLocalTimeContact

@[expose] public section

/-! The physical canonical contact measure has the original transported
local-time increments and is carried by physical visits to the site.
Its canonical value equals the reference canonical value at the actual
inverse clock, without changing the speed-mass normalization. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal

theorem reversibleResistanceCanonicalLocalTime_contact (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      ∃ h : HasContinuousOccupationLocalTime a (resistancePhysicalBandMass A a)
          (reversibleResistanceCanonicalPath A x ω),
        let ν := continuousPathLocalTimeMeasure h (fun _r hr => (resistancePhysicalBandMass_pos A a hr).le)
        ν.support ⊆ {t : ℝ | 0 ≤ t ∧ reversibleResistancePath A x t.toNNReal ω = a} ∧
          (∀ s t : ℝ≥0, ν (Ioc s.val t.val) =
            ENNReal.ofReal (reversibleResistanceLocalTime A x a t ω - reversibleResistanceLocalTime A x a s ω)) ∧
          ∀ t : ℝ, ν {t} = 0 := by
  filter_upwards [reversibleResistanceCanonicalLocalTime_identification A x ha] with ω hi
  refine ⟨hi.1, continuousPathLocalTimeMeasure_support hi.1 _, ?_,
    fun t => continuousPathLocalTimeMeasure_singleton hi.1 _ t⟩
  intro s t
  rw [continuousPathLocalTimeMeasure_Ioc]
  have he (r : ℝ≥0) : continuousPathLocalTime a (resistancePhysicalBandMass A a)
      (reversibleResistanceCanonicalPath A x ω) r = reversibleResistanceLocalTime A x a r ω :=
    (hi.1.value_eq r).symm.trans (hi.2 r)
  rw [he s, he t]

theorem reversibleResistanceCanonicalLocalTime_reference (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t : ℝ≥0,
      reversibleResistanceCanonicalLocalTime A x a t ω =
        reflectedCanonicalLocalTime A.resistanceLength A.resistanceLength_pos 1
          (A.resistance x) (A.resistance a) (reversibleResistanceInversePath A x t ω) ω := by
  filter_upwards [reversibleResistanceCanonicalLocalTime_identification A x ha,
    reflectedCanonicalLocalTime_identification A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) ⟨A.resistance a, reversibleResistance_site_interior A ha⟩]
    with ω hp hr t
  rw [hp.2 t, hr.2]
  rfl

end TimeTraps.Probability

end
