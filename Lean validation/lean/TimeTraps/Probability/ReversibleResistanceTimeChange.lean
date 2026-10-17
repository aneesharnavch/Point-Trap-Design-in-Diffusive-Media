module

public import TimeTraps.Analysis.ReversibleResistanceCoordinateInverse
public import TimeTraps.Probability.ReflectedPositiveTimeChangeMeasurablePath

@[expose] public section

/-! A concrete resistance/time-change construction from the original medium.
The reference reflected path has diffusivity one in resistance coordinates.
The literal clock integrates `(a * rho) ∘ R⁻¹`; its measurable inverse version
agrees with the literal inverse on the existing Brownian regular event. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def reversibleResistanceReference (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  foldedTrajectory A.resistanceLength 1 (A.resistance x) brownianDyadicPath t ω

noncomputable def reversibleResistanceClock (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ≥0 :=
  reflectedPositiveTimeClock A.resistanceLength 1 (A.resistance x)
    brownianDyadicPath A.resistanceSpeed t ω

noncomputable def reversibleResistanceInverseClock (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ≥0 :=
  reflectedPositiveTimeInverse A.resistanceLength 1 (A.resistance x)
    brownianDyadicPath A.resistanceSpeed t ω

noncomputable def reversibleResistanceInversePath (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ≥0 :=
  reflectedPositiveTimeInversePath A.resistanceLength 1 (A.resistance x)
    A.resistanceSpeed t ω

noncomputable def reversibleResistancePath (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  A.resistanceInverse
    (reversibleResistanceReference A x (reversibleResistanceInversePath A x t ω) ω)

theorem reversibleResistanceReference_mem (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceReference A x t ω ∈ Icc 0 A.resistanceLength :=
  foldedTrajectory_mem A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath t ω

theorem reversibleResistanceReference_jointlyMeasurable (A : IntervalMedium) (x : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reversibleResistanceReference A x p.1 p.2) :=
  foldedTrajectory_joint_measurable A.resistanceLength 1 (A.resistance x)
    brownianDyadicPath brownianDyadicPath_jointly_measurable

theorem reversibleResistanceClock_coe (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) :
    (reversibleResistanceClock A x t ω : ℝ) =
      ∫ r in (0 : ℝ)..t.val, A.conductance
        (A.resistanceInverse (reversibleResistanceReference A x r.toNNReal ω)) *
          A.source.density (A.resistanceInverse
            (reversibleResistanceReference A x r.toNNReal ω)) :=
  reflectedPositiveTimeClock_coe A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      (fun y _ => A.resistanceSpeed_pos y) t ω

theorem reversibleResistanceClock_jointlyMeasurable (A : IntervalMedium) (x : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reversibleResistanceClock A x p.1 p.2) :=
  reflectedPositiveTimeClock_jointlyMeasurable brownianDyadicPath_jointly_measurable
    A.resistanceLength A.resistanceLength_pos 1 (A.resistance x)
      A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn

theorem reversibleResistanceInversePath_zero (A : IntervalMedium) (x : ℝ) (ω : ℕ → ℝ) :
    reversibleResistanceInversePath A x 0 ω = 0 := by
  by_cases hω : BrownianDyadicRegular ω
  · rw [reversibleResistanceInversePath, reflectedPositiveTimeInversePath, if_pos hω]
    rw [congrFun (reflectedPositiveTimeInverse_eq A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
          ω hω.continuous) 0]
    exact PositiveTimeSpeed.inverse_zero _
  · simp only [reversibleResistanceInversePath, reflectedPositiveTimeInversePath, if_neg hω]

end TimeTraps.Probability
