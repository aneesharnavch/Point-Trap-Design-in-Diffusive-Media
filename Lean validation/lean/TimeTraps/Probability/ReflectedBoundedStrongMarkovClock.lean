module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovClockData
public import TimeTraps.Probability.ReversibleResistanceLifetimeRunningCost

@[expose] public section

/-! The literal positive resistance clock restarted along the same
reference trajectory. Its ordinary inverse reconstructs the actual
physical future path, simultaneously at all starting and future times.
These path identities do not assume a Markov property for the time change. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

def reversibleResistanceRestartClock (A : IntervalMedium) (x : ℝ)
    (s t : ℝ≥0) (ω : ℕ → ℝ) : ℝ≥0 :=
  Real.toNNReal (∫ r in (0 : ℝ)..t.val,
    A.resistanceSpeed (reversibleResistanceReference A x (s + r.toNNReal) ω))

def reversibleResistanceRestartInverse (A : IntervalMedium) (x : ℝ)
    (s t : ℝ≥0) (ω : ℕ → ℝ) : ℝ≥0 :=
  Function.invFun (fun u => reversibleResistanceRestartClock A x s u ω) t

def reversibleResistanceRestartPath (A : IntervalMedium) (x : ℝ)
    (s t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  A.resistanceInverse (reversibleResistanceReference A x
    (s + reversibleResistanceRestartInverse A x s t ω) ω)

theorem reversibleResistanceRestartClock_coe (A : IntervalMedium) (x : ℝ)
    (s t : ℝ≥0) (ω : ℕ → ℝ) :
    (reversibleResistanceRestartClock A x s t ω : ℝ) =
      ∫ r in (0 : ℝ)..t.val,
        A.resistanceSpeed (reversibleResistanceReference A x (s + r.toNNReal) ω) :=
  Real.coe_toNNReal _ (intervalIntegral.integral_nonneg_of_forall t.coe_nonneg
    (fun _ => (A.resistanceSpeed_pos _).le))

theorem reversibleResistanceRestartClock_eq (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s : ℝ≥0) :
    (fun t => reversibleResistanceRestartClock A x s t ω) =
      ((reversibleLifetimeSpeed A x hω).restart s).clock := by
  funext t
  apply NNReal.eq
  rw [reversibleResistanceRestartClock_coe, PositiveTimeSpeed.clock_coe]
  rfl

theorem reversibleResistanceRestartInverse_eq (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s : ℝ≥0) :
    (fun t => reversibleResistanceRestartInverse A x s t ω) =
      ((reversibleLifetimeSpeed A x hω).restart s).inverse := by
  change Function.invFun (fun t => reversibleResistanceRestartClock A x s t ω) = _
  rw [reversibleResistanceRestartClock_eq A x hω s]
  exact Function.invFun_eq_of_injective_of_rightInverse
    (PositiveTimeSpeed.clock_strictMono _).injective (PositiveTimeSpeed.clock_inverse _)

theorem reversibleResistanceClock_restart (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s t : ℝ≥0) :
    reversibleResistanceClock A x (s + t) ω =
      reversibleResistanceClock A x s ω + reversibleResistanceRestartClock A x s t ω := by
  have he := (reversibleLifetimeSpeed A x hω).restart_clock s t
  rw [reversibleLifetimeSpeed_clock A x hω,
    ← reversibleResistanceRestartClock_eq A x hω s] at he
  exact he

theorem reversibleResistanceInversePath_restart (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s t : ℝ≥0) :
    reversibleResistanceInversePath A x (reversibleResistanceClock A x s ω + t) ω =
      s + reversibleResistanceRestartInverse A x s t ω := by
  have he := (reversibleLifetimeSpeed A x hω).inverse_restart s t
  rw [reversibleLifetimeSpeed_clock A x hω, reversibleLifetimeSpeed_inverse A x hω,
    ← reversibleResistanceRestartInverse_eq A x hω s] at he
  exact he

theorem reversibleResistanceInversePath_add (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s t : ℝ≥0) :
    reversibleResistanceInversePath A x (s + t) ω =
      reversibleResistanceInversePath A x s ω + reversibleResistanceRestartInverse A x
        (reversibleResistanceInversePath A x s ω) t ω := by
  have he := (reversibleLifetimeSpeed A x hω).inverse_add s t
  rw [reversibleLifetimeSpeed_inverse A x hω,
    reversibleLifetimeSpeed_inverse A x hω,
    ← reversibleResistanceRestartInverse_eq A x hω] at he
  exact he

theorem reversibleResistancePath_restart (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s t : ℝ≥0) :
    reversibleResistancePath A x (s + t) ω =
      reversibleResistanceRestartPath A x (reversibleResistanceInversePath A x s ω) t ω := by
  change A.resistanceInverse (reversibleResistanceReference A x
    (reversibleResistanceInversePath A x (s + t) ω) ω) = _
  rw [reversibleResistanceInversePath_add A x hω s t]
  rfl

theorem reversibleResistance_restart_ae (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ s t : ℝ≥0,
      reversibleResistanceClock A x (s + t) ω =
        reversibleResistanceClock A x s ω + reversibleResistanceRestartClock A x s t ω ∧
      reversibleResistanceInversePath A x (s + t) ω =
        reversibleResistanceInversePath A x s ω + reversibleResistanceRestartInverse A x
          (reversibleResistanceInversePath A x s ω) t ω ∧
      reversibleResistancePath A x (s + t) ω =
        reversibleResistanceRestartPath A x (reversibleResistanceInversePath A x s ω) t ω := by
  filter_upwards [brownianDyadic_regular_ae] with ω hω
  exact fun s t => ⟨reversibleResistanceClock_restart A x hω s t,
    reversibleResistanceInversePath_add A x hω s t, reversibleResistancePath_restart A x hω s t⟩

end TimeTraps.Probability

end
