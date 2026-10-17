module

public import TimeTraps.Probability.ReflectedKilledL2Operator

@[expose] public section

/-! The killed expectation operator on the original Lebesgue interval
L² space. The same-function normalization changes both squared norms by
the same factor L, so the contraction constant remains one. Continuous
inputs retain the literal survival-weighted expectation representative. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reflectedKilledValue_product_memLp (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    MemLp (fun p : ℝ × (ℕ → ℝ) => reflectedKilledValue P T f p.1 p.2) 2
      ((reflectedUniformLaw P.length P.length_pos).prod brownianDyadicMeasure) :=
  MemLp.of_bound (reflectedKilledValue_measurable P T f).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (fun p => reflectedKilledValue_bound P T f p.1 p.2))

theorem reflectedKilledExpectation_interval_integrable (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    IntervalIntegrable (reflectedKilledExpectation P T f) volume 0 P.length ∧
      IntervalIntegrable (fun x => (reflectedKilledExpectation P T f x) ^ 2) volume 0 P.length := by
  have hm : MemLp (reflectedKilledExpectation P T f) 2 (volume.restrict (Ioc 0 P.length)) :=
    MemLp.of_bound (reflectedKilledExpectation_measurable P T f).aestronglyMeasurable ‖f‖
      (Eventually.of_forall (reflectedKilledExpectation_bound P T f))
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le P.length_pos.le).mpr
      (hm.integrable (by norm_num)),
    (intervalIntegrable_iff_integrableOn_Ioc_of_le P.length_pos.le).mpr hm.integrable_sq⟩

def reflectedKilledIntervalL2Operator (P : SpectralProblem n) (T : ℝ≥0) :
    IntervalSobolevL2 0 P.length →L[ℝ] IntervalSobolevL2 0 P.length :=
  (reflectedUniformL2Equiv P.length P.length_pos).toContinuousLinearMap.comp
    ((reflectedKilledL2Operator P T).comp
      (reflectedUniformL2Equiv P.length P.length_pos).symm.toContinuousLinearMap)

theorem reflectedKilledIntervalL2Operator_contraction (P : SpectralProblem n) (T : ℝ≥0)
    (f : IntervalSobolevL2 0 P.length) : ‖reflectedKilledIntervalL2Operator P T f‖ ≤ ‖f‖ := by
  let E := reflectedUniformL2Equiv P.length P.length_pos
  have hf : ‖f‖ ^ 2 = P.length * ‖E.symm f‖ ^ 2 := by
    have he := reflectedUniformL2Equiv_norm_sq P.length P.length_pos (E.symm f)
    change ‖E (E.symm f)‖ ^ 2 = P.length * ‖E.symm f‖ ^ 2 at he
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using he
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖E (reflectedKilledL2Operator P T (E.symm f))‖ ^ 2 ≤ ‖f‖ ^ 2
  rw [reflectedUniformL2Equiv_norm_sq, hf]
  apply mul_le_mul_of_nonneg_left _ P.length_pos.le
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (reflectedKilledL2Operator_contraction P T (E.symm f))

theorem reflectedKilledIntervalL2Operator_norm_le_one (P : SpectralProblem n) (T : ℝ≥0) :
    ‖reflectedKilledIntervalL2Operator P T‖ ≤ 1 := by
  apply (reflectedKilledIntervalL2Operator P T).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using reflectedKilledIntervalL2Operator_contraction P T f

theorem reflectedKilledIntervalL2Operator_continuous_input (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    reflectedKilledIntervalL2Operator P T
      (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) =
        reflectedUniformL2Equiv P.length P.length_pos (reflectedKilledContinuousL2 P T f) := by
  change reflectedUniformL2Equiv P.length P.length_pos
    (reflectedKilledL2Operator P T ((reflectedUniformL2Equiv P.length P.length_pos).symm
      (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, reflectedKilledL2Operator_continuous_input]

theorem reflectedKilledIntervalL2Operator_continuous_coe (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    (reflectedKilledIntervalL2Operator P T
      (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) : ℝ → ℝ)
        =ᵐ[volume.restrict (Ioo 0 P.length)] reflectedKilledExpectation P T f := by
  rw [reflectedKilledIntervalL2Operator_continuous_input]
  exact (reflectedUniformL2Equiv_coe P.length P.length_pos _).trans
    ((reflectedUniformLaw_ae_iff P.length P.length_pos _).mp (reflectedKilledContinuousL2_coe P T f))

end TimeTraps.Probability

end
