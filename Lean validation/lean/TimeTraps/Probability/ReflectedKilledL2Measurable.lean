module

public import TimeTraps.Probability.ReflectedAtomicWeightedValue
public import TimeTraps.Probability.ReflectedGaussianL2Feller
public import TimeTraps.Spectral.PhysicalProblem

@[expose] public section

/-! Literal survival-weighted values are jointly measurable in the start
and Brownian outcome. Their expectations are bounded measurable spatial
functions; no continuity in the local-time level or Markov property of
the killed process is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {n : ℕ}

theorem reflectedInteriorOccupationCoefficient_start_measurable (σ L a : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) =>
      reflectedInteriorOccupationCoefficient p.1 σ L a T p.2) := by
  have hm := (affineBrownianRegulator_start_jointlyMeasurable σ L 0 T).comp
    ((measurable_fst.sub_const a).prodMk measurable_snd)
  have hp := (affineBrownianRegulator_start_jointlyMeasurable σ L 0 T).comp
    ((measurable_fst.add_const a).prodMk measurable_snd)
  exact (hm.add hp).div_const (σ ^ 2)

theorem reflectedAtomicSurvival_start_measurable (L D : ℝ) (a κ : ι → ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedAtomicSurvival L D p.1 a κ T p.2) := by
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedAtomicHazard L D p.1 a κ T p.2) := by
    unfold reflectedAtomicHazard weightedContactHazard
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul
      (reflectedInteriorOccupationCoefficient_start_measurable (Real.sqrt (2 * D)) L (a i) T)
  exact hm.neg.exp

def reflectedKilledValue (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) (ω : ℕ → ℝ) : ℝ :=
  reflectedAtomicWeightedValue (reflectedFellerExtension P.length P.length_pos f)
    P.length P.diffusivity x P.site P.strength T ω

def reflectedKilledExpectation (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) : ℝ :=
  ∫ ω, reflectedKilledValue P T f x ω ∂brownianDyadicMeasure

theorem reflectedKilledValue_measurable (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedKilledValue P T f p.1 p.2) := by
  have hB := (brownianDyadicPath_jointly_measurable.comp
    (measurable_const.prodMk measurable_snd) :
      Measurable (fun p : ℝ × (ℕ → ℝ) => brownianDyadicPath T p.2))
  have hX : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      foldedTrajectory P.length P.diffusivity p.1 brownianDyadicPath T p.2) :=
    (reflectedFold_measurable P.length).comp
      (measurable_fst.add (measurable_const.mul hB))
  exact (reflectedAtomicSurvival_start_measurable P.length P.diffusivity P.site P.strength T).mul
    ((reflectedFellerExtension P.length P.length_pos f).continuous.measurable.comp hX)

theorem reflectedKilledValue_bound (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) (ω : ℕ → ℝ) :
    ‖reflectedKilledValue P T f x ω‖ ≤ ‖f‖ := by
  have hw := reflectedAtomicSurvival_bounds P.length P.diffusivity_pos x P.site P.strength
    (fun i => (P.strength_pos i).le) T ω
  have hf := reflectedFellerExtension_bound P.length P.length_pos f
    (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω)
  change ‖reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength T ω *
    reflectedFellerExtension P.length P.length_pos f
      (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω)‖ ≤ ‖f‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hw.1]
  exact (mul_le_mul_of_nonneg_right hw.2 (norm_nonneg _)).trans (by simpa using hf)

theorem reflectedKilledValue_memLp (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    MemLp (reflectedKilledValue P T f x) 2 brownianDyadicMeasure := by
  apply MemLp.of_bound ((reflectedKilledValue_measurable P T f).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (reflectedKilledValue_bound P T f x)

theorem reflectedKilledExpectation_measurable (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) : Measurable (reflectedKilledExpectation P T f) :=
  (reflectedKilledValue_measurable P T f).stronglyMeasurable.integral_prod_right'.measurable

theorem reflectedKilledExpectation_bound (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    ‖reflectedKilledExpectation P T f x‖ ≤ ‖f‖ := by
  have he := norm_integral_le_of_norm_le_const
    (μ := brownianDyadicMeasure) (C := ‖f‖)
    (Eventually.of_forall (reflectedKilledValue_bound P T f x))
  change ‖∫ ω, reflectedKilledValue P T f x ω ∂brownianDyadicMeasure‖ ≤ ‖f‖
  simpa only [MeasureTheory.probReal_univ, mul_one] using he

theorem reflectedKilledExpectation_memLp (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    MemLp (reflectedKilledExpectation P T f) 2 (reflectedUniformLaw P.length P.length_pos) :=
  MemLp.of_bound (reflectedKilledExpectation_measurable P T f).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (reflectedKilledExpectation_bound P T f))

end TimeTraps.Probability

end
