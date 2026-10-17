module

public import TimeTraps.Probability.KillingLifetimeTimeChangeIntegralData

@[expose] public section

/-! Whole pre-lifetime integral substitution and its exact integrability
equivalence. The source lifetime may be infinite and the time test may
have either sign. The Jacobian is the actual continuous positive speed. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem positiveClockReal_inverse (v : PositiveTimeSpeed) {s : ℝ} (hs : 0 ≤ s) :
    v.inverse (positiveClockReal v s).toNNReal = s.toNNReal := by
  have he : (positiveClockReal v s).toNNReal = v.clock s.toNNReal :=
    (congrArg Real.toNNReal (positiveClockReal_eq v hs)).trans (Real.toNNReal_coe (r := v.clock s.toNNReal))
  exact (congrArg v.inverse he).trans (v.inverse_clock s.toNNReal)

theorem positiveClock_integral_before (v : PositiveTimeSpeed) (g : ℝ≥0 → ℝ)
    {τ : WithTop ℝ} (hτ : 0 ≤ τ) :
    (∫ t in positiveTimeBefore (positiveClockLifetimeMap v.clock τ), g (v.inverse t.toNNReal)) =
      ∫ s in positiveTimeBefore τ, g s.toNNReal * v.rate s.toNNReal := by
  have hs := positiveTimeBefore_measurableSet τ
  have hd (s : ℝ) (_hs : s ∈ positiveTimeBefore τ) :
      HasDerivWithinAt (positiveClockReal v) (v.rate s.toNNReal) (positiveTimeBefore τ) s :=
    (positiveClockReal_hasDerivAt v s).hasDerivWithinAt
  have hinj : InjOn (positiveClockReal v) (positiveTimeBefore τ) :=
    (positiveClockReal_strictMonoOn v).injOn.mono (fun _ hx => hx.1.le)
  have hi := integral_image_eq_integral_abs_deriv_smul hs hd hinj
    (fun t : ℝ => g (v.inverse t.toNNReal))
  rw [positiveClockReal_image_before v hτ] at hi
  refine hi.trans ?_
  apply setIntegral_congr_fun hs
  intro s hst
  change |v.rate s.toNNReal| * g (v.inverse (positiveClockReal v s).toNNReal) =
    g s.toNNReal * v.rate s.toNNReal
  rw [positiveClockReal_inverse v hst.1.le, abs_of_pos (v.rate_pos _), mul_comm]

theorem positiveClock_integrable_before_iff (v : PositiveTimeSpeed) (g : ℝ≥0 → ℝ)
    {τ : WithTop ℝ} (hτ : 0 ≤ τ) :
    IntegrableOn (fun t : ℝ => g (v.inverse t.toNNReal))
      (positiveTimeBefore (positiveClockLifetimeMap v.clock τ)) ↔
        IntegrableOn (fun s : ℝ => g s.toNNReal * v.rate s.toNNReal) (positiveTimeBefore τ) := by
  have hs := positiveTimeBefore_measurableSet τ
  have hd (s : ℝ) (_hs : s ∈ positiveTimeBefore τ) :
      HasDerivWithinAt (positiveClockReal v) (v.rate s.toNNReal) (positiveTimeBefore τ) s :=
    (positiveClockReal_hasDerivAt v s).hasDerivWithinAt
  have hinj : InjOn (positiveClockReal v) (positiveTimeBefore τ) :=
    (positiveClockReal_strictMonoOn v).injOn.mono (fun _ hx => hx.1.le)
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd hinj
    (fun t : ℝ => g (v.inverse t.toNNReal))
  rw [positiveClockReal_image_before v hτ] at hi
  refine hi.trans (integrableOn_congr_fun (fun s hst => ?_) hs)
  change |v.rate s.toNNReal| * g (v.inverse (positiveClockReal v s).toNNReal) =
    g s.toNNReal * v.rate s.toNNReal
  rw [positiveClockReal_inverse v hst.1.le, abs_of_pos (v.rate_pos _), mul_comm]

end TimeTraps.Probability
