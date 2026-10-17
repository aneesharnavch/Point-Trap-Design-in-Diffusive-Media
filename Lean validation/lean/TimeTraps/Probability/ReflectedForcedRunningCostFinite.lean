module

public import TimeTraps.Probability.ReflectedForcedRunningCostData
public import TimeTraps.Probability.ReflectedFiniteKinkKilling

@[expose] public section

/-! The actual finite-time running-cost identity for every continuous
signed source and every solution of its original full-H1 weak equation.
The derived kink representation supplies the original reflection and
contact conditions; the Brownian integral is the constructed one. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {g u : ℝ → ℝ}

def reflectedForcedRunningCostIntegrand (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  reflectedAtomicSurvivalMultiplier P.length P.length_pos P.diffusivity P.diffusivity_pos
    x P.site P.strength (fun i => (P.strength_pos i).le)
    (reflectedFiniteKinkC2Integrand (hu.kinkBase_contDiff hg)
      P.length P.length_pos P.diffusivity P.diffusivity_pos P.site
      hu.kinkCoefficient P.site_interior x T)

theorem reflectedForcedRunningCost_finite (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    (fun ω => reflectedAtomicWeightedValue u P.length P.diffusivity x P.site P.strength T ω -
      u (reflectedFold P.length x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedForcedRunningCostIntegrand hu hg x T) ω -
        ∫ r in (0 : ℝ)..T.val,
          reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω) := by
  filter_upwards [reflectedFiniteKinkC2_killed_formula (hu.kinkBase_contDiff hg)
    P.length P.length_pos P.diffusivity P.diffusivity_pos P.site hu.kinkCoefficient
    P.strength P.site_interior (fun i => (P.strength_pos i).le) x T
    (hu.kinkSlope_endpoints hg).1 (hu.kinkSlope_endpoints hg).2
    (hu.kinkPotential_reaction hg)] with ω hf
  have hd : P.diffusivity * (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength r.toNNReal ω *
        deriv (deriv (hu.kinkBase hg))
          (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal ω)) =
      -(∫ r in (0 : ℝ)..T.val,
        reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r _
    calc
      _ = reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength r.toNNReal ω *
          (P.diffusivity * deriv (deriv (hu.kinkBase hg))
            (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal ω)) := by ring
      _ = _ := by
        rw [hu.kinkBase_source hg
          (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath r.toNNReal ω)]
        unfold reflectedAtomicWeightedValue
        ring
  have hv := hu.kinkPotential_eq hg
    (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)
  have hx := hu.kinkPotential_eq hg (reflectedFold_mem P.length P.length_pos x)
  change finiteKinkPotential (hu.kinkBase hg) Finset.univ P.site hu.kinkCoefficient _ = _ at hv hx
  rw [hd, hv, hx] at hf
  exact hf

theorem reflectedForcedRunningCost_state_memLp (hu : WeakForcedEquation P g u)
    (x : ℝ) (T : ℝ≥0) :
    MemLp (reflectedAtomicWeightedValue u P.length P.diffusivity x P.site P.strength T)
      2 brownianDyadicMeasure := by
  apply reflectedForcedRunningCost_memLp (P := P) _ x T
  simpa only [uIcc_of_le P.length_pos.le] using hu.energy.continuousOn

theorem reflectedForcedRunningCost_expected_finite (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
      ∂brownianDyadicMeasure) =
      u (reflectedFold P.length x) -
        reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T := by
  have hV := (reflectedForcedRunningCost_state_memLp hu x T).integrable (by norm_num)
  have hI := (Lp.memLp (brownianIntegral brownianDyadicPath_isPreBrownianReal
    (reflectedForcedRunningCostIntegrand hu hg x T))).integrable (by norm_num)
  have hA := reflectedForcedRunningCost_time_integral_integrable hg x T
  have he := integral_congr_ae (reflectedForcedRunningCost_finite hu hg x T)
  rw [integral_sub hV (integrable_const _), integral_sub hI hA,
    brownianIntegral_mean brownianDyadicPath_isPreBrownianReal] at he
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, zero_sub] at he
  change reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T -
    u (reflectedFold P.length x) = _ at he
  linarith

theorem reflectedForcedRunningCost_expected_time_finite (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal) =
      u (reflectedFold P.length x) -
        reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T := by
  rw [← reflectedForcedRunningCost_mean_time_integral hg x T]
  exact reflectedForcedRunningCost_expected_finite hu hg x T

end TimeTraps.Probability

end
