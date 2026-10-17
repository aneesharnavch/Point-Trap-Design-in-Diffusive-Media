module

public import TimeTraps.Probability.ReflectedKilledPointEvaluationData

@[expose] public section

/-! A fixed positive-time killed expectation is bounded by the actual
Lebesgue L² norm of its continuous input. The constant is the square root
of the finite reference-density bound; it may depend on time and start. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

def reflectedKilledPointConstant (P : SpectralProblem n) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) : ℝ :=
  Real.sqrt ‖reflectedKilledPointDensity P T hT x‖

theorem reflectedKilledPointConstant_nonneg (P : SpectralProblem n) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    0 ≤ reflectedKilledPointConstant P T hT x := Real.sqrt_nonneg _

theorem reflectedKilledPoint_input_norm_sq (P : SpectralProblem n)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    ‖reflectedUniformL2Equiv P.length P.length_pos
      (reflectedFellerToL2 P.length P.length_pos f)‖ ^ 2 =
        ∫ y in Ioo 0 P.length, (reflectedFellerExtension P.length P.length_pos f y) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reflectedUniformL2Equiv_coe P.length P.length_pos
    (reflectedFellerToL2 P.length P.length_pos f),
    (reflectedUniformLaw_ae_iff P.length P.length_pos _).mp
      (reflectedFellerToL2_coe P.length P.length_pos f)] with y he hf
  simp only [he, hf, Real.inner_apply, pow_two]

theorem reflectedKilledPoint_continuous_bound (P : SpectralProblem n) (T : ℝ≥0) (hT : 0 < T)
    (x : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    ‖reflectedKilledExpectation P T f x‖ ≤ reflectedKilledPointConstant P T hT x *
      ‖reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)‖ := by
  have he := (reflectedKilledExpectation_sq_le P T f x).trans
    (reflectedKilledPoint_kernel_sq_bound P T hT x f)
  rw [← reflectedKilledPoint_input_norm_sq P f] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (reflectedKilledPointConstant_nonneg P T hT x) (norm_nonneg _))).mp
  rw [mul_pow, reflectedKilledPointConstant, Real.sq_sqrt (norm_nonneg _)]
  simpa only [Real.norm_eq_abs, sq_abs] using he

end TimeTraps.Probability

end
