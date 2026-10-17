module

public import TimeTraps.Probability.KillingLifetimeTimeChange
public import TimeTraps.Probability.ReversibleResistanceTimeChangeAtomicHazardPaths
public import TimeTraps.Probability.ReflectedAtomicLifetimeConvention

@[expose] public section

/-! The physical first-attainment lifetime of the constructed reversible
resistance diffusion is the original clock evaluated at the reference
first-attainment lifetime. This is an equality of extended times on one
Brownian regular event for every threshold, including infinite lifetimes. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

noncomputable def reversibleResistanceAtomicClock (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (r : ℝ) (ω : ℕ → ℝ) : ℝ :=
  reversibleResistanceAtomicHazard A x a κ r.toNNReal ω

noncomputable def reversibleResistanceAttainmentLifetime (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (p : (ℕ → ℝ) × ℝ) : WithTop ℝ :=
  contactAttainmentLifetime (reversibleResistanceAtomicClock A x a κ) p

noncomputable def reversibleResistanceAttainmentLifetimeValue (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (p : (ℕ → ℝ) × ℝ) : ℝ≥0∞ :=
  nonnegativeLifetimeValue (reversibleResistanceAttainmentLifetime A x a κ p)

theorem reversibleResistanceAttainmentLifetime_nonneg (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (p : (ℕ → ℝ) × ℝ) :
    (0 : WithTop ℝ) ≤ reversibleResistanceAttainmentLifetime A x a κ p :=
  attainmentKillingTime_nonneg _ _

theorem reversibleResistanceAttainmentLifetime_clock (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (E : ℝ) :
    reversibleResistanceAttainmentLifetime A x a κ (ω, E) =
      positiveClockLifetimeMap (fun s => reversibleResistanceClock A x s ω)
        (reflectedAtomicAttainmentLifetime A.resistanceLength 1 (A.resistance x)
          (fun i => A.resistance (a i)) κ (ω, E)) := by
  let v := reflectedPositiveTimeSpeed A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) ω hω.continuous
  have hi (t : ℝ≥0) : reversibleResistanceInversePath A x t ω = v.inverse t := by
    change reflectedPositiveTimeInversePath A.resistanceLength 1 (A.resistance x)
      A.resistanceSpeed t ω = v.inverse t
    rw [reflectedPositiveTimeInversePath, if_pos hω]
    exact congrFun (reflectedPositiveTimeInverse_eq A.resistanceLength A.resistanceLength_pos 1
      (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) ω hω.continuous) t
  have hc : (fun s => reversibleResistanceClock A x s ω) = v.clock :=
    reflectedPositiveTimeClock_eq A.resistanceLength A.resistanceLength_pos 1
      (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) ω hω.continuous
  have hA : (fun r => reversibleResistanceAtomicClock A x a κ r ω) =
      fun r => reflectedAtomicClock A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ (v.orderIso.symm r.toNNReal : ℝ) ω := by
    funext r
    change reversibleResistanceAtomicHazard A x a κ r.toNNReal ω = _
    rw [reversibleResistanceAtomicHazard_reference, hi]
    change reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
      (fun i => A.resistance (a i)) κ (v.inverse r.toNNReal) ω =
      reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ ((v.orderIso.symm r.toNNReal : ℝ).toNNReal) ω
    rw [Real.toNNReal_coe]
    rfl
  change attainmentKillingTime (fun r => reversibleResistanceAtomicClock A x a κ r ω) E = _
  rw [hA]
  refine (attainmentKillingTime_inverse v.orderIso
    (fun r => reflectedAtomicClock A.resistanceLength 1 (A.resistance x)
      (fun i => A.resistance (a i)) κ r ω) E).trans ?_
  rw [hc]
  rfl

theorem reversibleResistanceAttainmentLifetime_clock_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ E : ℝ,
      reversibleResistanceAttainmentLifetime A x a κ (ω, E) =
        positiveClockLifetimeMap (fun s => reversibleResistanceClock A x s ω)
          (reflectedAtomicAttainmentLifetime A.resistanceLength 1 (A.resistance x)
            (fun i => A.resistance (a i)) κ (ω, E)) := by
  filter_upwards [brownianDyadic_regular_ae] with ω hω
  exact reversibleResistanceAttainmentLifetime_clock A x a κ hω

theorem reversibleResistanceAttainmentLifetime_clock_product_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    reversibleResistanceAttainmentLifetime A x a κ
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        (fun p => positiveClockLifetimeMap (fun s => reversibleResistanceClock A x s p.1)
          (reflectedAtomicAttainmentLifetime A.resistanceLength 1 (A.resistance x)
            (fun i => A.resistance (a i)) κ p)) := by
  have h := (Measure.quasiMeasurePreserving_fst (μ := brownianDyadicMeasure) (ν := expMeasure 1)).ae
    (reversibleResistanceAttainmentLifetime_clock_ae A x a κ)
  filter_upwards [h] with p hp
  exact hp p.2

end TimeTraps.Probability
