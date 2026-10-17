module

public import TimeTraps.Probability.ReflectedGaussianL2Feller
public import TimeTraps.Probability.ReflectedFellerCosine
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact cosine moments and products for the actual normalized uniform
measure. The constant mode has mass one and every nonconstant cosine has
mean zero. These identities supply the normalization of the actual L2
cosine basis. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedUniform_cosine_integral (L : ℝ) (hL : 0 < L) (n : ℤ) :
    (∫ x, Real.cos (((n : ℝ) * Real.pi / L) * x) ∂reflectedUniformLaw L hL) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hc : (n : ℝ) * Real.pi / L ≠ 0 :=
      div_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hn) Real.pi_ne_zero) hL.ne'
    have hi : (∫ x in (0 : ℝ)..L, Real.cos (((n : ℝ) * Real.pi / L) * x)) = 0 := by
      rw [intervalIntegral.integral_comp_mul_left _ hc, integral_cos]
      simp only [mul_zero, div_mul_cancel₀ _ hL.ne', Real.sin_int_mul_pi, Real.sin_zero,
        sub_zero, smul_zero]
    rw [if_neg hn, reflectedUniformLaw, integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hL.le, hi, smul_zero]

theorem reflectedUniform_neumannCosine_integral (L : ℝ) (hL : 0 < L) (n : ℤ) :
    (∫ x, reflectedFellerExtension L hL (neumannCosine L n) x ∂reflectedUniformLaw L hL) =
      if n = 0 then 1 else 0 := by
  rw [← reflectedUniform_cosine_integral L hL n]
  apply integral_congr_ae
  filter_upwards [reflectedUniformLaw_ae_mem L hL] with x hx
  exact reflectedFellerExtension_on_interval L hL (neumannCosine L n) ⟨x, hx⟩

theorem reflectedFellerToL2_inner (L : ℝ) (hL : 0 < L) (f g : C(Icc (0 : ℝ) L, ℝ)) :
    inner ℝ (reflectedFellerToL2 L hL f) (reflectedFellerToL2 L hL g) =
      ∫ x, reflectedFellerExtension L hL (f * g) x ∂reflectedUniformLaw L hL := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reflectedFellerToL2_coe L hL f, reflectedFellerToL2_coe L hL g] with x hx hy
  rw [hx, hy, Real.inner_apply]
  rfl

theorem reflectedFellerToL2_cosine_inner (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    inner ℝ (reflectedFellerToL2 L hL (neumannCosine L m))
      (reflectedFellerToL2 L hL (neumannCosine L n)) =
      if m = n then (if n = 0 then 1 else 1 / 2) else 0 := by
  have hi (k : ℤ) : Integrable (reflectedFellerExtension L hL (neumannCosine L k))
      (reflectedUniformLaw L hL) := by
    apply (integrable_const ‖neumannCosine L k‖).mono'
      (reflectedFellerExtension L hL (neumannCosine L k)).continuous.aestronglyMeasurable
    exact Eventually.of_forall (reflectedFellerExtension_bound L hL (neumannCosine L k))
  rw [reflectedFellerToL2_inner, neumannCosine_mul]
  change (∫ x, (1 / 2 : ℝ) *
    (reflectedFellerExtension L hL (neumannCosine L ((m : ℤ) - n)) x +
      reflectedFellerExtension L hL (neumannCosine L ((m : ℤ) + n)) x)
    ∂reflectedUniformLaw L hL) = _
  rw [integral_const_mul, integral_add (hi _) (hi _),
    reflectedUniform_neumannCosine_integral, reflectedUniform_neumannCosine_integral]
  by_cases hmn : m = n
  · subst m
    by_cases hn : n = 0
    · norm_num [hn]
    · have hs : (n : ℤ) + n ≠ 0 := by omega
      simp [hn, hs]
  · have hd : (m : ℤ) - n ≠ 0 := by omega
    have hs : (m : ℤ) + n ≠ 0 := by omega
    simp [hmn, hd, hs]

end TimeTraps.Probability
