module

public import TimeTraps.Probability.KillingLifetimeTimeChangeIntegral
public import TimeTraps.Probability.ReversibleResistanceLifetimeTimeChange

@[expose] public section

/-! Actual pathwise running-cost substitution up to an arbitrary extended
reference lifetime, followed by the literal physical killing lifetime.
Infinite lifetimes and signed costs are retained. The separate exact
integrability equivalence prevents treating undefined integrals as finite. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

noncomputable def reversibleLifetimeSpeed (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) : PositiveTimeSpeed :=
  reflectedPositiveTimeSpeed A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) ω hω.continuous

theorem reversibleLifetimeSpeed_clock (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) :
    (reversibleLifetimeSpeed A x hω).clock = fun s => reversibleResistanceClock A x s ω :=
  (reflectedPositiveTimeClock_eq A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) ω hω.continuous).symm

theorem reversibleLifetimeSpeed_inverse (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (t : ℝ≥0) :
    (reversibleLifetimeSpeed A x hω).inverse t = reversibleResistanceInversePath A x t ω := by
  change (reversibleLifetimeSpeed A x hω).inverse t =
    reflectedPositiveTimeInversePath A.resistanceLength 1 (A.resistance x) A.resistanceSpeed t ω
  rw [reflectedPositiveTimeInversePath, if_pos hω]
  exact (congrFun (reflectedPositiveTimeInverse_eq A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) ω hω.continuous) t).symm

theorem reversibleResistancePath_integral_before_clock (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (g : ℝ → ℝ)
    {τ : WithTop ℝ} (hτ : 0 ≤ τ) :
    (∫ t in positiveTimeBefore (positiveClockLifetimeMap (fun s => reversibleResistanceClock A x s ω) τ),
      g (reversibleResistancePath A x t.toNNReal ω)) =
      ∫ s in positiveTimeBefore τ,
        g (A.resistanceInverse (reversibleResistanceReference A x s.toNNReal ω)) *
          A.resistanceSpeed (reversibleResistanceReference A x s.toNNReal ω) := by
  have hi := positiveClock_integral_before (reversibleLifetimeSpeed A x hω)
    (fun s => g (A.resistanceInverse (reversibleResistanceReference A x s ω))) hτ
  rw [reversibleLifetimeSpeed_clock A x hω] at hi
  simp only [reversibleLifetimeSpeed_inverse A x hω] at hi
  convert! hi using 1

theorem reversibleResistancePath_integrable_before_clock_iff (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (g : ℝ → ℝ)
    {τ : WithTop ℝ} (hτ : 0 ≤ τ) :
    IntegrableOn (fun t : ℝ => g (reversibleResistancePath A x t.toNNReal ω))
      (positiveTimeBefore (positiveClockLifetimeMap (fun s => reversibleResistanceClock A x s ω) τ)) ↔
      IntegrableOn (fun s : ℝ =>
        g (A.resistanceInverse (reversibleResistanceReference A x s.toNNReal ω)) *
          A.resistanceSpeed (reversibleResistanceReference A x s.toNNReal ω)) (positiveTimeBefore τ) := by
  have hi := positiveClock_integrable_before_iff (reversibleLifetimeSpeed A x hω)
    (fun s => g (A.resistanceInverse (reversibleResistanceReference A x s ω))) hτ
  rw [reversibleLifetimeSpeed_clock A x hω] at hi
  simp only [reversibleLifetimeSpeed_inverse A x hω] at hi
  convert! hi using 1

theorem reversibleResistancePath_cost_before_attainment (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (E : ℝ) (g : ℝ → ℝ) :
    (∫ t in positiveTimeBefore (reversibleResistanceAttainmentLifetime A x a κ (ω, E)),
      g (reversibleResistancePath A x t.toNNReal ω)) =
      ∫ s in positiveTimeBefore (reflectedAtomicAttainmentLifetime A.resistanceLength 1
        (A.resistance x) (fun i => A.resistance (a i)) κ (ω, E)),
        g (A.resistanceInverse (reversibleResistanceReference A x s.toNNReal ω)) *
          A.resistanceSpeed (reversibleResistanceReference A x s.toNNReal ω) := by
  rw [reversibleResistanceAttainmentLifetime_clock A x a κ hω E]
  exact reversibleResistancePath_integral_before_clock A x hω g (attainmentKillingTime_nonneg _ _)

theorem reversibleResistancePath_cost_integrable_before_attainment_iff (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (E : ℝ) (g : ℝ → ℝ) :
    IntegrableOn (fun t : ℝ => g (reversibleResistancePath A x t.toNNReal ω))
      (positiveTimeBefore (reversibleResistanceAttainmentLifetime A x a κ (ω, E))) ↔
      IntegrableOn (fun s : ℝ =>
        g (A.resistanceInverse (reversibleResistanceReference A x s.toNNReal ω)) *
          A.resistanceSpeed (reversibleResistanceReference A x s.toNNReal ω))
        (positiveTimeBefore (reflectedAtomicAttainmentLifetime A.resistanceLength 1
          (A.resistance x) (fun i => A.resistance (a i)) κ (ω, E))) := by
  rw [reversibleResistanceAttainmentLifetime_clock A x a κ hω E]
  exact reversibleResistancePath_integrable_before_clock_iff A x hω g (attainmentKillingTime_nonneg _ _)

theorem reversibleResistancePath_cost_before_attainment_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure, ∀ g : ℝ → ℝ,
      (∫ t in positiveTimeBefore (reversibleResistanceAttainmentLifetime A x a κ p),
        g (reversibleResistancePath A x t.toNNReal p.1)) =
        ∫ s in positiveTimeBefore (reflectedAtomicAttainmentLifetime A.resistanceLength 1
          (A.resistance x) (fun i => A.resistance (a i)) κ p),
          g (A.resistanceInverse (reversibleResistanceReference A x s.toNNReal p.1)) *
            A.resistanceSpeed (reversibleResistanceReference A x s.toNNReal p.1) := by
  have h := (Measure.quasiMeasurePreserving_fst (μ := brownianDyadicMeasure) (ν := expMeasure 1)).ae
    brownianDyadic_regular_ae
  filter_upwards [h] with p hp
  exact fun g => reversibleResistancePath_cost_before_attainment A x a κ hp p.2 g

end TimeTraps.Probability
