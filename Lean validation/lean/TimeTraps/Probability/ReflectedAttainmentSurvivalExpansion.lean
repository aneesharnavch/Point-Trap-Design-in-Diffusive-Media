module

public import TimeTraps.Probability.ReflectedSurvivalExpansion
public import TimeTraps.Probability.ReflectedAtomicLifetimeConvention

@[expose] public section

/-! The every-start expansion applies to the paper's literal first
attainment of the independent exponential threshold. Equality of the
two lifetime conventions was proved almost surely as an extended value. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {n : ℕ}

noncomputable def reflectedAtomicAttainmentSurvivalProbability (L D x : ℝ)
    (a κ : ι → ℝ) (T : ℝ≥0) : ℝ :=
  (exponentialKillingMeasure brownianDyadicMeasure
    {p | (T.val : WithTop ℝ) < reflectedAtomicAttainmentLifetime L D x a κ p}).toReal

theorem reflectedAtomicAttainmentSurvivalProbability_eq (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    reflectedAtomicAttainmentSurvivalProbability L D x a κ T =
      reflectedAtomicSurvivalProbability L D x a κ T := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  apply eventuallyEq_set.mpr
  filter_upwards [reflectedAtomicLifetime_eq_attainment_ae L hL D hD x a κ hκ] with p hp
  rw [hp]

theorem reflectedAtomicAttainmentSurvivalProbability_expansion_bound (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) (hT : 1 ≤ T) :
    |reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x P.site P.strength T -
      Real.exp (-P.principalValue * T.val) * reflectedSurvivalFirstCoefficient P x| ≤
      reflectedSurvivalRemainderConstant P x *
        Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val) := by
  rw [reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos P.diffusivity
    P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le)]
  exact reflectedAtomicSurvivalProbability_expansion_bound P hx T hT

theorem reflectedAtomicAttainmentSurvivalProbability_expansion (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    0 < reflectedSurvivalFirstCoefficient P x ∧
      P.principalValue < (P.intervalPointProblem.spectralEnumeration 1).1⁻¹ ∧
      Asymptotics.IsBigO atTop
        (fun T : ℝ≥0 => reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity
          x P.site P.strength T - Real.exp (-P.principalValue * T.val) *
            reflectedSurvivalFirstCoefficient P x)
        (fun T : ℝ≥0 => Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val)) := by
  have he (T : ℝ≥0) := reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos
    P.diffusivity P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le) T
  simp only [he]
  exact reflectedAtomicSurvivalProbability_expansion P hx

end TimeTraps.Probability
