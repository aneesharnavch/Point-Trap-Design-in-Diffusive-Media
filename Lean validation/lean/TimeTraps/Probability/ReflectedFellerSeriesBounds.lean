module

public import TimeTraps.Probability.ReflectedFellerDomainIdentification
public import TimeTraps.Probability.ReflectedCosineIntegrals
public import Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section

/-! Uniform coefficient bounds and genuinely summable Gaussian decay
for the continuous-function heat series. Orthogonality is transported
from the independently checked actual uniform integral identities. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped Topology

theorem reflectedFeller_cosine_norm_le_one (L : ℝ) (n : ℤ) : ‖neumannCosine L n‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  exact Real.abs_cos_le_one _

theorem reflectedFellerMean_norm (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) : ‖reflectedFellerMean L hL f‖ ≤ ‖f‖ := by
  rw [reflectedFellerMean_uniform]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := reflectedUniformLaw L hL)
      (Eventually.of_forall (reflectedFellerExtension_bound L hL f))

theorem reflectedFellerPairing_cosine_norm (L : ℝ) (hL : 0 < L)
    (n : ℕ) (f : C(Icc (0 : ℝ) L, ℝ)) :
    ‖reflectedFellerPairing L hL (neumannCosine L n) f‖ ≤ ‖f‖ := by
  rw [reflectedFellerPairing_apply]
  calc
    _ ≤ ‖neumannCosine L n * f‖ := reflectedFellerMean_norm L hL _
    _ ≤ ‖neumannCosine L n‖ * ‖f‖ := norm_mul_le _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (reflectedFeller_cosine_norm_le_one L n) (norm_nonneg f)
    _ = ‖f‖ := one_mul _

theorem reflectedFellerPairing_cosine_cosine (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    reflectedFellerPairing L hL (neumannCosine L m) (neumannCosine L n) =
      if m = n then (if n = 0 then 1 else 1 / 2) else 0 := by
  rw [reflectedFellerPairing_apply, reflectedFellerMean_uniform, ← reflectedFellerToL2_inner]
  exact reflectedFellerToL2_cosine_inner L hL m n

theorem reflectedFellerPairing_cosine_one (L : ℝ) (hL : 0 < L) (n : ℕ) :
    reflectedFellerPairing L hL (neumannCosine L n) 1 = if n = 0 then 1 else 0 := by
  rw [← neumannCosine_zero L]
  simpa only [Nat.cast_zero, if_true] using reflectedFellerPairing_cosine_cosine L hL n 0

def reflectedFellerHeatRate (L D : ℝ) : ℝ := D * (Real.pi / L) ^ 2

theorem reflectedFellerHeatRate_pos (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) :
    0 < reflectedFellerHeatRate L D :=
  mul_pos hD (sq_pos_of_pos (div_pos Real.pi_pos hL))

theorem reflectedFeller_gaussian_weight_summable (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * (n : ℝ) ^ 2)) := by
  apply (Real.summable_pow_mul_exp_neg_nat_mul k hc).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) k) (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg n) k)
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [pow_two]
    exact_mod_cast Nat.le_mul_self n
  nlinarith

theorem reflectedFeller_gaussian_decay_mono (c : ℝ) (hc : 0 ≤ c)
    (n : ℕ) (δ t : ℝ) (ht : δ ≤ t) :
    Real.exp (-c * (n : ℝ) ^ 2 * t) ≤ Real.exp (-(c * δ) * (n : ℝ) ^ 2) := by
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonneg_left ht (mul_nonneg hc (sq_nonneg (n : ℝ)))
  nlinarith

end TimeTraps.Probability

end
