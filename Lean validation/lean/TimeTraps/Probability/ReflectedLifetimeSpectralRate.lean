module

public import TimeTraps.Probability.ReflectedGroundSurvivalBounds
public import TimeTraps.Probability.ReflectedAtomicLifetimeSurvival
public import TimeTraps.Analysis.ExponentialSurvivalRate

@[expose] public section

/-! The literal lifetime survival probability has the physical
principal Rayleigh value as its logarithmic decay rate. The proof uses
the actual eigenfunction expectation and compact positive ground bounds.
It does not assert the stronger two-eigenvalue survival expansion. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {n : ℕ}

noncomputable def reflectedAtomicSurvivalProbability (L D x : ℝ) (a κ : ι → ℝ) (T : ℝ≥0) : ℝ :=
  (exponentialKillingMeasure brownianDyadicMeasure
    {p | (T.val : WithTop ℝ) < reflectedAtomicLifetime L D x a κ p}).toReal

theorem reflectedAtomicSurvivalProbability_eq (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    reflectedAtomicSurvivalProbability L D x a κ T = reflectedAtomicMeanSurvival L D x a κ T := by
  have he := congrArg ENNReal.toReal
    (reflectedAtomicLifetime_survival_probability L hL D hD x a κ hκ T.val T.coe_nonneg)
  have ht : T.val.toNNReal = T := Real.toNNReal_coe
  have hc := congrArg (fun t : ℝ≥0 => (ENNReal.ofReal (reflectedAtomicMeanSurvival L D x a κ t)).toReal) ht
  exact he.trans (hc.trans (ENNReal.toReal_ofReal (reflectedAtomicMeanSurvival_bounds L hD x a κ hκ T).1))

theorem reflectedPrincipal_lifetime_survival_bounds (P : SpectralProblem n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ Icc 0 P.length, ∀ T : ℝ≥0,
      c * Real.exp (-P.principalValue * T.val) ≤
        reflectedAtomicSurvivalProbability P.length P.diffusivity x P.site P.strength T ∧
      reflectedAtomicSurvivalProbability P.length P.diffusivity x P.site P.strength T ≤
        C * Real.exp (-P.principalValue * T.val) := by
  obtain ⟨c, C, hc, hC, hb⟩ := reflectedPrincipal_survival_uniform_bounds P
  refine ⟨c, C, hc, hC, ?_⟩
  intro x hx T
  rw [reflectedAtomicSurvivalProbability_eq P.length P.length_pos P.diffusivity P.diffusivity_pos
    x P.site P.strength (fun i => (P.strength_pos i).le)]
  exact hb x hx T

theorem reflectedPrincipal_mean_survival_log_rate (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Tendsto (fun T : ℝ≥0 =>
      -Real.log (reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength T) / T.val)
      atTop (𝓝 P.principalValue) := by
  obtain ⟨c, C, hc, hC, hb⟩ := reflectedPrincipal_survival_uniform_bounds P
  exact exponentialSurvivalRate hc hC (hb x hx)

theorem reflectedPrincipal_lifetime_survival_log_rate (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Tendsto (fun T : ℝ≥0 =>
      -Real.log (reflectedAtomicSurvivalProbability P.length P.diffusivity x P.site P.strength T) / T.val)
      atTop (𝓝 P.principalValue) := by
  obtain ⟨c, C, hc, hC, hb⟩ := reflectedPrincipal_lifetime_survival_bounds P
  exact exponentialSurvivalRate hc hC (hb x hx)

end TimeTraps.Probability
