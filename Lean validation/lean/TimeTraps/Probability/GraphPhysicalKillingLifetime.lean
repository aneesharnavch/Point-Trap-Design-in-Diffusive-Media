module

public import TimeTraps.Probability.BorelSpeedLifetime
public import TimeTraps.Probability.GraphAtomicKillingLifetime
public import TimeTraps.Probability.GraphPhysicalClock

@[expose] public section

/-! Literal first threshold attainment in physical time is the physical
clock evaluated at reference-time attainment, with infinity preserved.
Its extended value is the accumulated original source before killing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

noncomputable def GraphShiftedContactOperatorProblem.physicalAtomicKillingClock
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (t : ℝ) (p : GraphContinuousPath P.geometry) : ℝ :=
  P.atomicKillingClock a κ (P.geometry.physicalInverseClock b hb t.toNNReal p : ℝ) p

noncomputable def GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetime
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) : WithTop ℝ :=
  contactAttainmentLifetime (P.physicalAtomicKillingClock b hb a κ) p

noncomputable def GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetimeValue
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) : ℝ≥0∞ :=
  nonnegativeLifetimeValue (P.physicalAtomicAttainmentLifetime b hb a κ p)

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetime_eq_clock
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) :
    P.physicalAtomicAttainmentLifetime b hb a κ p =
      positiveClockLifetimeMap (fun t => P.geometry.physicalClock b hb t p.1)
        (P.atomicAttainmentLifetime a κ p) :=
  attainmentKillingTime_inverse (P.geometry.physicalClockSpeed b hb p.1).orderIso
    (fun t => P.atomicKillingClock a κ t p.1) p.2

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetime_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) :
    (0 : WithTop ℝ) ≤ P.physicalAtomicAttainmentLifetime b hb a κ p :=
  attainmentKillingTime_nonneg _ _

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetime_eq_top_iff
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) :
    P.physicalAtomicAttainmentLifetime b hb a κ p = ⊤ ↔ P.atomicAttainmentLifetime a κ p = ⊤ := by
  rw [P.physicalAtomicAttainmentLifetime_eq_clock, positiveClockLifetimeMap_eq_top_iff]

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetimeValue_integral
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ)
    (p : GraphContinuousPath P.geometry × ℝ) :
    P.physicalAtomicAttainmentLifetimeValue b hb a κ p =
      ∫⁻ r in positiveTimeBefore (P.atomicAttainmentLifetime a κ p),
        ENNReal.ofReal (P.geometry.physicalSpeed b (p.1 r.toNNReal)) := by
  change nonnegativeLifetimeValue (P.physicalAtomicAttainmentLifetime b hb a κ p) = _
  rw [P.physicalAtomicAttainmentLifetime_eq_clock]
  exact borelSpeed_lifetime_value (P.geometry.physicalClockSpeed b hb p.1)
    (P.atomicAttainmentLifetime_nonneg a κ p)

end TimeTraps.Analysis
