module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimePaths

@[expose] public section

/-! Exact clock identities used to transport contact time measures. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

theorem reversibleResistanceInversePath_clock (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s : ℝ≥0) :
    reversibleResistanceInversePath A x (reversibleResistanceClock A x s ω) ω = s := by
  let v := reflectedPositiveTimeSpeed A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
        ω hω.continuous
  have hI := congrFun (reflectedPositiveTimeInverse_eq A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
        ω hω.continuous) (reversibleResistanceClock A x s ω)
  have hC := congrFun (reflectedPositiveTimeClock_eq A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
        ω hω.continuous) s
  change reversibleResistanceClock A x s ω = v.clock s at hC
  simp only [reversibleResistanceInversePath, reflectedPositiveTimeInversePath, if_pos hω]
  exact hI.trans ((congrArg v.inverse hC).trans (v.inverse_clock s))

theorem reversibleResistancePath_clock (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s : ℝ≥0) :
    reversibleResistancePath A x (reversibleResistanceClock A x s ω) ω =
      A.resistanceInverse (reversibleResistanceReference A x s ω) := by
  rw [reversibleResistancePath, reversibleResistanceInversePath_clock A x hω s]

theorem reversibleResistanceClock_real_measurable (A : IntervalMedium) (x : ℝ) (ω : ℕ → ℝ) :
    Measurable (fun r : ℝ => (reversibleResistanceClock A x r.toNNReal ω : ℝ)) := by
  let q : ℝ → ℝ≥0 × (ℕ → ℝ) := fun r => (r.toNNReal, ω)
  have hq : Measurable q := continuous_real_toNNReal.measurable.prodMk measurable_const
  have hc := (reversibleResistanceClock_jointlyMeasurable A x).comp hq
  dsimp only [Function.comp_def, q] at hc
  exact NNReal.continuous_coe.measurable.comp hc

theorem reversibleResistanceClock_preimage_Ioc (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (S T : ℝ≥0) :
    (fun r : ℝ => (reversibleResistanceClock A x r.toNNReal ω : ℝ)) ⁻¹' Ioc S.val T.val =
      Ioc (reversibleResistanceInversePath A x S ω).val (reversibleResistanceInversePath A x T ω).val := by
  let v := reflectedPositiveTimeSpeed A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
        ω hω.continuous
  have hC (s : ℝ≥0) : reversibleResistanceClock A x s ω = v.clock s :=
    congrFun (reflectedPositiveTimeClock_eq A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
          ω hω.continuous) s
  have hI (t : ℝ≥0) : reversibleResistanceInversePath A x t ω = v.inverse t := by
    simp only [reversibleResistanceInversePath, reflectedPositiveTimeInversePath, if_pos hω]
    exact congrFun (reflectedPositiveTimeInverse_eq A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
          ω hω.continuous) t
  ext r
  change ((S : ℝ) < (reversibleResistanceClock A x r.toNNReal ω : ℝ) ∧
      (reversibleResistanceClock A x r.toNNReal ω : ℝ) ≤ (T : ℝ)) ↔ _
  rw [hC, hI S, hI T]
  have hl : S < v.clock r.toNNReal ↔ v.inverse S < r.toNNReal := by
    simpa only [v.clock_inverse] using
      (v.clock_strictMono.lt_iff_lt (a := v.inverse S) (b := r.toNNReal))
  have hu : v.clock r.toNNReal ≤ T ↔ r.toNNReal ≤ v.inverse T := by
    simpa only [v.clock_inverse] using
      (v.clock_strictMono.le_iff_le (a := r.toNNReal) (b := v.inverse T))
  exact and_congr (hl.trans Real.lt_toNNReal_iff_coe_lt) (hu.trans Real.toNNReal_le_iff_le_coe)

end TimeTraps.Probability
