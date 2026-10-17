module

public import TimeTraps.Probability.ReflectedRobinSurvivalSeries

@[expose] public section

/-! The actual first-attainment survival series in increasing natural
spectral order, at every physical start and positive time. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal

variable {n : ℕ}

theorem reflectedRobinAttainmentSurvival_hasSum_enumeration (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    HasSum (fun k : ℕ =>
      (∫ y in (0 : ℝ)..P.length,
        (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration k)).representative
          P.length_pos y) *
        Real.exp (-(P.intervalPointProblem.spectralEnumeration k).1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration k)).representative
          P.length_pos x)
      (reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x
        (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) :=
  P.intervalPointProblem.spectralEnumeration.hasSum_iff.mpr
    (reflectedRobinAttainmentSurvival_hasSum_at_start P T hT hx)

theorem reflectedRobinAttainmentSurvival_series (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x
      (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T =
      ∑' k : ℕ, (∫ y in (0 : ℝ)..P.length,
        (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration k)).representative
          P.length_pos y) *
        Real.exp (-(P.intervalPointProblem.spectralEnumeration k).1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration k)).representative
          P.length_pos x :=
  (reflectedRobinAttainmentSurvival_hasSum_enumeration P T hT hx).tsum_eq.symm

end TimeTraps.Probability
