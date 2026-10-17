module

public import TimeTraps.Probability.ReflectedRobinKilledL2Measurable
public import TimeTraps.Probability.ReflectedBrownianMarginal
public import TimeTraps.Probability.ReflectedUniformL2Normalization

@[expose] public section

/-! The actual killed expectation is dominated in squared norm by the
unkilled reflected average of the squared input. Cauchy--Schwarz, the
literal survival bound, and proved uniform invariance give contraction.
The endpoint/time-zero cases are included in the actual Gaussian laws. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reflectedRobinKilledExpectation_sq_le (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    (reflectedRobinKilledExpectation P T f x) ^ 2 ≤
      ∫ y, (reflectedFellerExtension P.length P.length_pos f y) ^ 2
        ∂reflectedGaussianLaw P.length x (Real.toNNReal (2 * P.diffusivity) * T) := by
  let g := reflectedFellerExtension P.length P.length_pos f
  let X := foldedTrajectory P.length P.diffusivity x brownianDyadicPath T
  have hX := foldedTrajectory_gaussian_hasLaw brownianDyadicPath_isPreBrownianReal
    P.length P.diffusivity P.diffusivity_pos x T
  have hg : MemLp (fun ω => g (X ω)) 2 brownianDyadicMeasure := by
    apply MemLp.of_bound (g.continuous.measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable ‖f‖
    exact Eventually.of_forall (fun ω => reflectedFellerExtension_bound P.length P.length_pos f (X ω))
  have hv := reflectedRobinKilledValue_memLp P T f x
  have hcs : (reflectedRobinKilledExpectation P T f x) ^ 2 ≤
      ∫ ω, (reflectedRobinKilledValue P T f x ω) ^ 2 ∂brownianDyadicMeasure := by
    have h := memLp_integral_mul_sq_le hv
      (memLp_const (μ := brownianDyadicMeasure) (p := 2) (1 : ℝ))
    change (∫ ω, reflectedRobinKilledValue P T f x ω ∂brownianDyadicMeasure) ^ 2 ≤ _
    simpa only [mul_one, one_pow, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, smul_eq_mul] using h
  have hm : (∫ ω, (reflectedRobinKilledValue P T f x ω) ^ 2 ∂brownianDyadicMeasure) ≤
      ∫ ω, (g (X ω)) ^ 2 ∂brownianDyadicMeasure := by
    apply integral_mono hv.integrable_sq hg.integrable_sq
    intro ω
    have hw := reflectedAtomicSurvival_bounds P.length P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight)
      (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg) T ω
    have hw2 : (reflectedAtomicSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω) ^ 2 ≤ 1 := by
      simpa only [one_pow] using (sq_le_sq₀ hw.1.le zero_le_one).mpr hw.2
    change (reflectedAtomicSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω * g (X ω)) ^ 2 ≤ _
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)).trans_eq (one_mul _)
  refine (hcs.trans hm).trans_eq ?_
  exact hX.integral_comp (g.continuous.pow 2).aestronglyMeasurable

theorem reflectedRobinKilledExpectation_uniform_sq (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    (∫ x, (reflectedRobinKilledExpectation P T f x) ^ 2 ∂reflectedUniformLaw P.length P.length_pos) ≤
      ∫ x, (reflectedFellerExtension P.length P.length_pos f x) ^ 2
        ∂reflectedUniformLaw P.length P.length_pos := by
  let g : ℝ → ℝ := fun x => (reflectedFellerExtension P.length P.length_pos f x) ^ 2
  have hg : Measurable g := (reflectedFellerExtension P.length P.length_pos f).continuous.measurable.pow_const 2
  have hb (x : ℝ) : ‖g x‖ ≤ ‖f‖ ^ 2 := by
    dsimp [g]
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [Real.norm_eq_abs, sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg f)).mpr
      (reflectedFellerExtension_bound P.length P.length_pos f x)
  have hk := reflectedGaussianAverage_memLp P.length P.length_pos
    (Real.toNNReal (2 * P.diffusivity) * T) hg hb
  calc
    _ ≤ ∫ x, (∫ y, g y ∂reflectedGaussianLaw P.length x
        (Real.toNNReal (2 * P.diffusivity) * T)) ∂reflectedUniformLaw P.length P.length_pos := by
      apply integral_mono (reflectedRobinKilledExpectation_memLp P T f).integrable_sq
        (hk.integrable (by norm_num))
      exact reflectedRobinKilledExpectation_sq_le P T f
    _ = _ := reflectedGaussianLaw_uniform_integral P.length P.length_pos
      (Real.toNNReal (2 * P.diffusivity) * T) hg hb

theorem reflectedRobinKilledExpectation_interval_sq (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    (∫ x in 0..P.length, (reflectedRobinKilledExpectation P T f x) ^ 2) ≤
      ∫ x in 0..P.length, (reflectedFellerExtension P.length P.length_pos f x) ^ 2 := by
  have h := reflectedRobinKilledExpectation_uniform_sq P T f
  have hn : 0 < ((ENNReal.ofReal P.length)⁻¹).toReal := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal P.length_pos.le]
    exact inv_pos.mpr P.length_pos
  simp only [reflectedUniformLaw, integral_smul_measure, smul_eq_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le P.length_pos.le] at h
  exact (mul_le_mul_iff_right₀ hn).mp h

end TimeTraps.Probability

end
