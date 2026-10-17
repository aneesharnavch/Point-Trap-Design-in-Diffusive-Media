module

public import TimeTraps.Probability.ReflectedRobinWeakFinite
public import TimeTraps.Analysis.ScalarSurvivalVolterra
public import TimeTraps.Spectral.RobinOperatorBridge

@[expose] public section

/-! The actual combined Robin killing evolves every original full-H1
Robin eigenstate by exp(-lambda t). Both boundary reactions are present
in the pathwise clock. No additional smoothness or endpoint conditions
are supplied by the caller. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {L D : ℝ} {a κ : ι → ℝ} {β₀ βL ev : ℝ} {u : ℝ → ℝ}

theorem ReflectedRobinWeakEquation.actual_eigen_volterra
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL (fun z => ev * u z) u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (x : ℝ) (T : ℝ≥0) :
    reflectedAtomicValueExpectation u L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) T =
      u (reflectedFold L x) - ev * ∫ r in (0 : ℝ)..T.val,
        reflectedAtomicValueExpectation u L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
          r.toNNReal := by
  have hc : ContinuousOn u (Icc 0 L) := by
    simpa only [uIcc_of_le hL.le] using hu.energy.continuousOn
  have he := hu.actual_expected_time_finite hL hD ha hκ hβ₀ hβL (hc.const_mul ev) x T
  simp only [reflectedRobinSurvival_eq_atomic L hD] at he
  have hs (r : ℝ) : (∫ ω,
      reflectedAtomicSurvival L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) r.toNNReal ω *
        (ev * u (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) ∂brownianDyadicMeasure) =
      ev * reflectedAtomicValueExpectation u L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
        r.toNNReal := by
    rw [reflectedAtomicValueExpectation, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun _ => by unfold reflectedAtomicWeightedValue; ring))
  simp only [hs, intervalIntegral.integral_const_mul] at he
  change ev * (∫ r in (0 : ℝ)..T.val, reflectedAtomicValueExpectation u L D x
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) r.toNNReal) =
      u (reflectedFold L x) - reflectedAtomicValueExpectation u L D x
        (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) T at he
  linarith

theorem ReflectedRobinWeakEquation.actual_eigen_expectation
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL (fun z => ev * u z) u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedRobinSurvival L D x a κ β₀ βL T ω *
      u (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure) =
      Real.exp (-ev * T.val) * u (reflectedFold L x) := by
  simp only [reflectedRobinSurvival_eq_atomic L hD]
  change reflectedAtomicValueExpectation u L D x (reflectedRobinSite L a)
    (reflectedRobinStrength κ β₀ βL) T = _
  have hc : ContinuousOn u (Icc 0 L) := by
    simpa only [uIcc_of_le hL.le] using hu.energy.continuousOn
  apply scalarSurvivalVolterra (reflectedRobinRunningCost_expectation_continuous L hL D hD
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
    (reflectedRobinStrength_nonneg hκ hβ₀ hβL) hc x)
  intro S
  exact hu.actual_eigen_volterra hL hD ha hκ hβ₀ hβL x S

variable {n : ℕ} {P : RobinProblem n}

theorem robinWeakEigenEquation_to_reflected (hu : RobinWeakEigenEquation P ev u) :
    ReflectedRobinWeakEquation P.length P.diffusivity P.site P.strength P.betaLeft P.betaRight
      (fun z => ev * u z) u := by
  refine ⟨hu.energy, ?_⟩
  intro v hv
  simpa only [mul_assoc, intervalIntegral.integral_const_mul] using hu.weak_form v hv

theorem reflectedRobinWeakEigenstate_expectation (hu : RobinWeakEigenEquation P ev u) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedRobinSurvival P.length P.diffusivity x P.site P.strength P.betaLeft P.betaRight T ω *
      u (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω) ∂brownianDyadicMeasure) =
      Real.exp (-ev * T.val) * u (reflectedFold P.length x) :=
  (robinWeakEigenEquation_to_reflected hu).actual_eigen_expectation P.length_pos P.diffusivity_pos
    P.site_interior (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg x T

theorem reflectedRobinWeakEigenstate_expectation_at_start (hu : RobinWeakEigenEquation P ev u)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) :
    (∫ ω, reflectedRobinSurvival P.length P.diffusivity x P.site P.strength P.betaLeft P.betaRight T ω *
      u (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω) ∂brownianDyadicMeasure) =
      Real.exp (-ev * T.val) * u x := by
  simpa only [reflectedFold_eq_self P.length P.length_pos x hx] using
    reflectedRobinWeakEigenstate_expectation hu x T

theorem reflectedRobinIntervalEigenstate_expectation (P : RobinProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedRobinSurvival P.length P.diffusivity x P.site P.strength P.betaLeft P.betaRight T ω *
      (P.intervalPointProblem.eigenstate i).representative P.length_pos
        (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω) ∂brownianDyadicMeasure) =
      Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x) :=
  reflectedRobinWeakEigenstate_expectation (P.interval_eigenbasis_weak i) x T

end TimeTraps.Probability
