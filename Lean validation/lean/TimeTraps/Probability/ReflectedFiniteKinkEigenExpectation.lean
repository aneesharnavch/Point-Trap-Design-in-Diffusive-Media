module

public import TimeTraps.Probability.ReflectedAtomicWeightedValueTime
public import TimeTraps.Probability.ReflectedFiniteKinkKilling
public import TimeTraps.Analysis.ScalarSurvivalVolterra

@[expose] public section

/-! Exact actual killed evolution of a finite-kink eigenfunction.
The spatial eigen-equation, contact reaction and reflecting slopes are
explicit here; the physical weak-eigenstate bridge discharges them.
The ordinary expectation and its exponential solution use proved finite
product integrability and the actual Brownian integral's zero mean. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkC2_eigen_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x ev : ℝ) (T : ℝ≥0)
    (hzero : finiteKinkSlope F Finset.univ a c 0 = 0)
    (hright : finiteKinkSlope F Finset.univ a c L = 0)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i))
    (hsource : ∀ z ∈ Icc 0 L,
      D * deriv (deriv F) z = -ev * finiteKinkPotential F Finset.univ a c z) :
    (fun ω => reflectedAtomicWeightedValue (finiteKinkPotential F Finset.univ a c) L D x a κ T ω -
      finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω -
        ev * ∫ r in (0 : ℝ)..T.val,
          reflectedAtomicWeightedValue (finiteKinkPotential F Finset.univ a c) L D x a κ r.toNNReal ω) := by
  filter_upwards [reflectedFiniteKinkC2_killed_formula hF L hL D hD a c κ ha hκ x T
    hzero hright hcontact] with ω hf
  have hd : D * (∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω *
      deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) =
      -ev * (∫ r in (0 : ℝ)..T.val,
        reflectedAtomicWeightedValue (finiteKinkPotential F Finset.univ a c) L D x a κ r.toNNReal ω) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    calc
      _ = reflectedAtomicSurvival L D x a κ r.toNNReal ω *
          (D * deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by ring
      _ = _ := by
        rw [hsource _ (foldedTrajectory_mem L hL D x brownianDyadicPath r.toNNReal ω)]
        unfold reflectedAtomicWeightedValue
        ring
  rw [hd] at hf
  exact hf.trans (by ring)

theorem reflectedFiniteKinkC2_eigen_volterra (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x ev : ℝ) (T : ℝ≥0)
    (hzero : finiteKinkSlope F Finset.univ a c 0 = 0)
    (hright : finiteKinkSlope F Finset.univ a c L = 0)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i))
    (hsource : ∀ z ∈ Icc 0 L,
      D * deriv (deriv F) z = -ev * finiteKinkPotential F Finset.univ a c z) :
    reflectedAtomicValueExpectation (finiteKinkPotential F Finset.univ a c) L D x a κ T =
      finiteKinkPotential F Finset.univ a c (reflectedFold L x) -
      ev * ∫ r in (0 : ℝ)..T.val,
        reflectedAtomicValueExpectation (finiteKinkPotential F Finset.univ a c) L D x a κ r.toNNReal := by
  have hc := finiteKinkPotential_continuous hF.continuous Finset.univ a c
  have hV := (reflectedAtomicWeightedValue_memLp hc L hL D hD x a κ hκ T).integrable (by norm_num)
  have hI := (Lp.memLp (brownianIntegral brownianDyadicPath_isPreBrownianReal
    (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ
      (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)))).integrable (by norm_num)
  have hA := (reflectedAtomicWeightedValue_time_integral_integrable hc L hL D hD x a κ hκ T).const_mul ev
  have he := integral_congr_ae (reflectedFiniteKinkC2_eigen_formula hF L hL D hD a c κ ha hκ x ev T
    hzero hright hcontact hsource)
  rw [integral_sub hV (integrable_const _), integral_sub hI hA,
    brownianIntegral_mean brownianDyadicPath_isPreBrownianReal, integral_const_mul,
    reflectedAtomicWeightedValue_mean_time_integral hc L hL D hD x a κ hκ T] at he
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, zero_sub] at he
  change reflectedAtomicValueExpectation (finiteKinkPotential F Finset.univ a c) L D x a κ T -
    finiteKinkPotential F Finset.univ a c (reflectedFold L x) =
    -(ev * ∫ r in (0 : ℝ)..T.val,
      reflectedAtomicValueExpectation (finiteKinkPotential F Finset.univ a c) L D x a κ r.toNNReal) at he
  linarith

theorem reflectedFiniteKinkC2_eigen_expectation (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x ev : ℝ) (T : ℝ≥0)
    (hzero : finiteKinkSlope F Finset.univ a c 0 = 0)
    (hright : finiteKinkSlope F Finset.univ a c L = 0)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i))
    (hsource : ∀ z ∈ Icc 0 L,
      D * deriv (deriv F) z = -ev * finiteKinkPotential F Finset.univ a c z) :
    reflectedAtomicValueExpectation (finiteKinkPotential F Finset.univ a c) L D x a κ T =
      Real.exp (-ev * T.val) * finiteKinkPotential F Finset.univ a c (reflectedFold L x) := by
  apply scalarSurvivalVolterra
    (reflectedAtomicValueExpectation_continuous
      (finiteKinkPotential_continuous hF.continuous Finset.univ a c) L hL D hD x a κ hκ)
  intro S
  exact reflectedFiniteKinkC2_eigen_volterra hF L hL D hD a c κ ha hκ x ev S
    hzero hright hcontact hsource

end TimeTraps.Probability
