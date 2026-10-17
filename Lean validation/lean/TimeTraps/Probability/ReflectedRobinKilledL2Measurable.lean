module

public import TimeTraps.Probability.ReflectedKilledL2Measurable
public import TimeTraps.Probability.ReflectedRobinEigenExpectation
public import TimeTraps.Probability.ReflectedGaussianL2Feller

@[expose] public section

/-! Literal Robin survival-weighted values are jointly measurable in the start
and Brownian outcome. Their expectations are bounded measurable spatial
functions; no continuity in the local-time level or Markov property of
the killed process is assumed. The original RobinProblem retains its
positive interior-contact count and both original endpoint coefficients. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

def reflectedRobinKilledValue (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) (ω : ℕ → ℝ) : ℝ :=
  reflectedAtomicWeightedValue (reflectedFellerExtension P.length P.length_pos f)
    P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω

def reflectedRobinKilledExpectation (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) : ℝ :=
  ∫ ω, reflectedRobinKilledValue P T f x ω ∂brownianDyadicMeasure

theorem reflectedRobinKilledValue_measurable (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedRobinKilledValue P T f p.1 p.2) := by
  have hB := (brownianDyadicPath_jointly_measurable.comp
    (measurable_const.prodMk measurable_snd) :
      Measurable (fun p : ℝ × (ℕ → ℝ) => brownianDyadicPath T p.2))
  have hX : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      foldedTrajectory P.length P.diffusivity p.1 brownianDyadicPath T p.2) :=
    (reflectedFold_measurable P.length).comp
      (measurable_fst.add (measurable_const.mul hB))
  exact (reflectedAtomicSurvival_start_measurable P.length P.diffusivity (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T).mul
    ((reflectedFellerExtension P.length P.length_pos f).continuous.measurable.comp hX)

theorem reflectedRobinKilledValue_bound (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) (ω : ℕ → ℝ) :
    ‖reflectedRobinKilledValue P T f x ω‖ ≤ ‖f‖ := by
  have hw := reflectedAtomicSurvival_bounds P.length P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight)
    (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg) T ω
  have hf := reflectedFellerExtension_bound P.length P.length_pos f
    (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω)
  change ‖reflectedAtomicSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω *
    reflectedFellerExtension P.length P.length_pos f
      (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω)‖ ≤ ‖f‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hw.1]
  exact (mul_le_mul_of_nonneg_right hw.2 (norm_nonneg _)).trans (by simpa using hf)

theorem reflectedRobinKilledValue_memLp (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    MemLp (reflectedRobinKilledValue P T f x) 2 brownianDyadicMeasure := by
  apply MemLp.of_bound ((reflectedRobinKilledValue_measurable P T f).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (reflectedRobinKilledValue_bound P T f x)

theorem reflectedRobinKilledExpectation_measurable (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) : Measurable (reflectedRobinKilledExpectation P T f) :=
  (reflectedRobinKilledValue_measurable P T f).stronglyMeasurable.integral_prod_right'.measurable

theorem reflectedRobinKilledExpectation_bound (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    ‖reflectedRobinKilledExpectation P T f x‖ ≤ ‖f‖ := by
  have he := norm_integral_le_of_norm_le_const
    (μ := brownianDyadicMeasure) (C := ‖f‖)
    (Eventually.of_forall (reflectedRobinKilledValue_bound P T f x))
  change ‖∫ ω, reflectedRobinKilledValue P T f x ω ∂brownianDyadicMeasure‖ ≤ ‖f‖
  simpa only [MeasureTheory.probReal_univ, mul_one] using he

theorem reflectedRobinKilledExpectation_memLp (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    MemLp (reflectedRobinKilledExpectation P T f) 2 (reflectedUniformLaw P.length P.length_pos) :=
  MemLp.of_bound (reflectedRobinKilledExpectation_measurable P T f).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (reflectedRobinKilledExpectation_bound P T f))

end TimeTraps.Probability

end
