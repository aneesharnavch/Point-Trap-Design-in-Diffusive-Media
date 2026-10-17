module

public import TimeTraps.Probability.ReflectedAtomicLifetimeConvention
public import TimeTraps.Probability.HomogeneousLifetimeObjective

@[expose] public section

/-! Ordinary expectation of the literal first-attainment lifetime for
the original homogeneous design. Almost-sure finiteness and integrability
are derived, and the expectation is the original full-H1 weak mean state.
The independent exponential threshold and occupation-clock normalization
are unchanged. No eventual killing assumption is added. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval
open scoped ENNReal

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

def homogeneousAttainmentLifetimeExpectation
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) : ℝ :=
  ∫ p, (reflectedAtomicAttainmentLifetimeValue L D x E.geometry.site E.strength p).toReal
    ∂exponentialKillingMeasure brownianDyadicMeasure

theorem homogeneousAttainmentLifetime_extended_mean
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    (∫⁻ p, reflectedAtomicAttainmentLifetimeValue L D x E.geometry.site E.strength p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ENNReal.ofReal (E.state (reflectedFold L x)) :=
  (lintegral_congr_ae (reflectedAtomicLifetimeValue_eq_attainment_ae L hL D hD x
    E.geometry.site E.strength (fun i => (E.strength_pos i).le)).symm).trans
      (reflectedWeakMeanTime_lifetime_extended_mean E x)

theorem homogeneousAttainmentLifetime_finite_mean
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    (∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetimeValue L D x E.geometry.site E.strength p < ∞) ∧
    Integrable (fun p =>
      (reflectedAtomicAttainmentLifetimeValue L D x E.geometry.site E.strength p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) ∧
    homogeneousAttainmentLifetimeExpectation E x = E.state (reflectedFold L x) :=
  extendedLifetime_finite_mean (exponentialKillingMeasure brownianDyadicMeasure)
    (reflectedAtomicAttainmentLifetimeValue L D x E.geometry.site E.strength)
    (reflectedAtomicAttainmentLifetimeValue_aemeasurable L hL D hD x E.geometry.site E.strength
      (fun i => (E.strength_pos i).le))
    (E.homogeneous_state_pos _ (reflectedFold_mem L hL x)).le
    (homogeneousAttainmentLifetime_extended_mean E x)

theorem homogeneousAttainmentLifetimeExpectation_eq
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    homogeneousAttainmentLifetimeExpectation E x = homogeneousLifetimeExpectation E x := by
  apply integral_congr_ae
  filter_upwards [reflectedAtomicLifetimeValue_eq_attainment_ae L hL D hD x
    E.geometry.site E.strength (fun i => (E.strength_pos i).le)] with p hp
  exact congrArg ENNReal.toReal hp.symm

theorem homogeneousAttainmentLifetimeExpectation_eqOn
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    EqOn (homogeneousAttainmentLifetimeExpectation E) E.state (Icc (0 : ℝ) L) := by
  intro x hx
  exact (homogeneousAttainmentLifetimeExpectation_eq E x).trans
    (homogeneousLifetimeExpectation_eqOn E hx)

theorem homogeneousAttainmentLifetimeExpectation_weak_equation
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    WeakIntervalEquation E.geometry E.strength (homogeneousAttainmentLifetimeExpectation E) := by
  have he : homogeneousAttainmentLifetimeExpectation E = homogeneousLifetimeExpectation E :=
    funext (homogeneousAttainmentLifetimeExpectation_eq E)
  rw [he]
  exact homogeneousLifetimeExpectation_weak_equation E

theorem homogeneousAttainmentLifetimeExpectation_intervalIntegrable
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    IntervalIntegrable (homogeneousAttainmentLifetimeExpectation E) volume 0 L := by
  have he : homogeneousAttainmentLifetimeExpectation E = homogeneousLifetimeExpectation E :=
    funext (homogeneousAttainmentLifetimeExpectation_eq E)
  rw [he]
  exact homogeneousLifetimeExpectation_intervalIntegrable E

end TimeTraps.Probability

end
