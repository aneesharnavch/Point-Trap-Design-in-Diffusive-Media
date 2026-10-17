module

public import TimeTraps.Probability.ReflectedWeakMeanTimeIntegral
public import TimeTraps.Probability.ReflectedAtomicLifetimeMean
public import TimeTraps.Probability.ExtendedLifetimeFiniteMean

@[expose] public section

/-! The original homogeneous full-H1 weak mean state is the actual mean
strict-threshold killing lifetime of the constructed reflected diffusion
with its normalized interior occupation clock. Infinite-horizon
integrability and almost-sure finite lifetime are conclusions. The
independent exponential threshold and the literal clock are retained. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

theorem reflectedWeakMeanTime_lifetime_extended_mean
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    (∫⁻ p, reflectedAtomicLifetimeValue L D x E.geometry.site E.strength p
      ∂exponentialKillingMeasure brownianDyadicMeasure) = ENNReal.ofReal (E.state (reflectedFold L x)) :=
  (reflectedAtomicLifetimeValue_mean_survival L hL D hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le)).trans (reflectedWeakMeanTime_mean_survival_integral E x).2.2

theorem reflectedWeakMeanTime_lifetime
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    (∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicLifetimeValue L D x E.geometry.site E.strength p < ∞) ∧
    Integrable (fun p => (reflectedAtomicLifetimeValue L D x E.geometry.site E.strength p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) ∧
    (∫ p, (reflectedAtomicLifetimeValue L D x E.geometry.site E.strength p).toReal
      ∂exponentialKillingMeasure brownianDyadicMeasure) = E.state (reflectedFold L x) :=
  extendedLifetime_finite_mean (exponentialKillingMeasure brownianDyadicMeasure)
    (reflectedAtomicLifetimeValue L D x E.geometry.site E.strength)
    (reflectedAtomicLifetimeValue_aemeasurable L hL D hD x E.geometry.site E.strength
      (fun i => (E.strength_pos i).le))
    (E.homogeneous_state_pos _ (reflectedFold_mem L hL x)).le
    (reflectedWeakMeanTime_lifetime_extended_mean E x)

theorem reflectedWeakMeanTime_lifetime_mean_at_start
    (E : IntervalDesign (homogeneous L D hL hD) n K) {x : ℝ} (hx : x ∈ Icc 0 L) :
    (∫ p, (reflectedAtomicLifetimeValue L D x E.geometry.site E.strength p).toReal
      ∂exponentialKillingMeasure brownianDyadicMeasure) = E.state x := by
  simpa only [reflectedFold_eq_self L hL x hx] using (reflectedWeakMeanTime_lifetime E x).2.2

theorem reflectedWeakMeanTime_path_survival_mean
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    (∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal
      (reflectedAtomicSurvival L D x E.geometry.site E.strength r.toNNReal ω))
      ∂brownianDyadicMeasure) = ENNReal.ofReal (E.state (reflectedFold L x)) := by
  rw [← reflectedAtomicLifetimeValue_mean_identity L hL D hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le)]
  exact reflectedWeakMeanTime_lifetime_extended_mean E x

end TimeTraps.Probability
