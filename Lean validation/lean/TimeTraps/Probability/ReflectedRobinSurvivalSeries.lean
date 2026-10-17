module

public import TimeTraps.Probability.ReflectedRobinSurvivalSeriesData

@[expose] public section

/-! The complete Robin eigenfunction series equals actual survival at
every start and every positive time. The same series gives survival of
the literal first-attainment lifetime of the independent exponential
threshold, with both original endpoint coefficients retained. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reflectedRobinAtomicMeanSurvival_hasSum (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      (∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate i).representative P.length_pos y) *
        Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x))
      (reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site)
        (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) := by
  simpa only [reflectedRobinSurvivalOne_eigenbasis_inner, reflectedRobinKilledPointEvaluation_survival] using
    reflectedRobinKilledPointEvaluation_hasSum P T hT x (reflectedRobinSurvivalOne P)

theorem reflectedRobinMeanSurvival_hasSum (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      (∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate i).representative P.length_pos y) *
        Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x))
      (∫ ω, reflectedRobinSurvival P.length P.diffusivity x P.site P.strength P.betaLeft P.betaRight T ω
        ∂brownianDyadicMeasure) := by
  simpa only [reflectedRobinSurvival_eq_atomic P.length P.diffusivity_pos,
    reflectedAtomicMeanSurvival] using reflectedRobinAtomicMeanSurvival_hasSum P T hT x

theorem reflectedRobinAttainmentSurvival_hasSum (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      (∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate i).representative P.length_pos y) *
        Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x))
      (reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x
        (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) := by
  rw [reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos P.diffusivity P.diffusivity_pos
    x _ _ (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg),
    reflectedAtomicSurvivalProbability_eq P.length P.length_pos P.diffusivity P.diffusivity_pos
      x _ _ (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg)]
  exact reflectedRobinAtomicMeanSurvival_hasSum P T hT x

theorem reflectedRobinAttainmentSurvival_hasSum_at_start (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      (∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate i).representative P.length_pos y) *
        Real.exp (-i.1⁻¹ * T.val) * (P.intervalPointProblem.eigenstate i).representative P.length_pos x)
      (reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x
        (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) := by
  simpa only [reflectedFold_eq_self P.length P.length_pos x hx] using
    reflectedRobinAttainmentSurvival_hasSum P T hT x

end TimeTraps.Probability
