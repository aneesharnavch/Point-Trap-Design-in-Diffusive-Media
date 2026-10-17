module

public import TimeTraps.Probability.ReversibleResistanceTimeChange
public import TimeTraps.Probability.ReflectedPositiveTimeChangePaths

@[expose] public section

/-! Path properties of the constructed resistance/time-change process.
Joint measurability holds for the chosen version, and its paths are continuous
even on the exceptional samples because the inverse-time version is then zero.
Its agreement with the literal inverse-clock formula is simultaneous in time.
No generator, Markov, or atomic-local-time identification is asserted. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistancePath_mem (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistancePath A x t ω ∈ Icc A.source.left A.source.right :=
  A.resistanceInverse_mem _

theorem reversibleResistancePath_coordinate (A : IntervalMedium) (x : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) :
    A.resistance (reversibleResistancePath A x t ω) =
      reversibleResistanceReference A x (reversibleResistanceInversePath A x t ω) ω :=
  A.resistance_inverse (reversibleResistanceReference_mem A x _ ω)

theorem reversibleResistancePath_jointlyMeasurable (A : IntervalMedium) (x : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reversibleResistancePath A x p.1 p.2) := by
  have hI : Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      reversibleResistanceInversePath A x p.1 p.2) :=
    reflectedPositiveTimeInversePath_jointlyMeasurable A.resistanceLength
      A.resistanceLength_pos 1 (A.resistance x) A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
  let q : ℝ≥0 × (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) :=
    fun p => (reversibleResistanceInversePath A x p.1 p.2, p.2)
  have hq : Measurable q := hI.prodMk measurable_snd
  have hY := (reversibleResistanceReference_jointlyMeasurable A x).comp hq
  dsimp only [Function.comp_def, q] at hY
  change Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => A.resistanceInverse
    (reversibleResistanceReference A x (reversibleResistanceInversePath A x p.1 p.2) p.2))
  exact A.resistanceInverse_continuous.measurable.comp hY

theorem reversibleResistancePath_continuous (A : IntervalMedium) (x : ℝ) (ω : ℕ → ℝ) :
    Continuous (fun t => reversibleResistancePath A x t ω) := by
  by_cases hω : BrownianDyadicRegular ω
  · have hY : Continuous (fun t => reversibleResistanceReference A x t ω) :=
      (reflectedFold_continuous A.resistanceLength).comp
        (continuous_const.add (continuous_const.mul hω.continuous))
    have hI : Continuous (fun t => reversibleResistanceInversePath A x t ω) :=
      reflectedPositiveTimeInversePath_continuous A.resistanceLength A.resistanceLength_pos
        1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
          (fun y _ => A.resistanceSpeed_pos y) ω
    exact A.resistanceInverse_continuous.comp (hY.comp hI)
  · simpa only [reversibleResistancePath, reversibleResistanceInversePath,
      reflectedPositiveTimeInversePath, if_neg hω] using
      (continuous_const : Continuous (fun _ : ℝ≥0 =>
        A.resistanceInverse (reversibleResistanceReference A x 0 ω)))

theorem reversibleResistancePath_initial_ae (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, reversibleResistancePath A x 0 ω = x := by
  filter_upwards [brownianDyadicPath_start_zero] with ω hω
  rw [reversibleResistancePath, reversibleResistanceInversePath_zero,
    reversibleResistanceReference,
    foldedTrajectory_initial A.resistanceLength A.resistanceLength_pos 1 (A.resistance x)
      (A.resistance_mem hx) brownianDyadicPath 0 ω hω]
  exact A.resistanceInverse_resistance hx

theorem reversibleResistancePath_literal_ae (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t,
      reversibleResistancePath A x t ω = A.resistanceInverse
        (reversibleResistanceReference A x (reversibleResistanceInverseClock A x t ω) ω) := by
  filter_upwards [reflectedPositiveTimeInversePath_eq_ae A.resistanceLength 1
    (A.resistance x) A.resistanceSpeed] with ω hω
  intro t
  change A.resistanceInverse (reversibleResistanceReference A x
    (reflectedPositiveTimeInversePath A.resistanceLength 1
      (A.resistance x) A.resistanceSpeed t ω) ω) = _
  rw [hω t]
  rfl

theorem reversibleResistanceClock_regular_ae (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun s => reversibleResistanceClock A x s ω) ∧
      StrictMono (fun s => reversibleResistanceClock A x s ω) ∧
      Tendsto (fun s => reversibleResistanceClock A x s ω) atTop atTop ∧
      Continuous (fun t => reversibleResistanceInverseClock A x t ω) ∧
      StrictMono (fun t => reversibleResistanceInverseClock A x t ω) ∧
      ∀ t, reversibleResistanceClock A x (reversibleResistanceInverseClock A x t ω) ω = t ∧
        reversibleResistanceInverseClock A x (reversibleResistanceClock A x t ω) ω = t :=
  reflectedPositiveTimeChange_regular_ae A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y)

end TimeTraps.Probability
