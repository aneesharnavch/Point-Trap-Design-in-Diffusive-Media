module

public import TimeTraps.Probability.ReflectedFellerNeumannGenerator

@[expose] public section

/-! Evaluation and time translation of the full C² Neumann Feller
variation identity. Only the given interior derivative identities and
continuous endpoint values of the Neumann data are required. -/

namespace TimeTraps.Probability

open MeasureTheory Set

theorem ReflectedNeumannC2.feller_integral_apply {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D) (t : ℝ) (ht : 0 ≤ t) (z : Icc (0 : ℝ) L) :
    reflectedFellerTimeOperator L hL D t F.valueMap z - F.valueMap z =
      D * ∫ r in 0..t, reflectedFellerTimeOperator L hL D r F.curvatureMap z := by
  have h := congrArg (fun f : C(Icc (0 : ℝ) L, ℝ) => f z) (F.feller_integral hL D hD t ht)
  have hi := (ContinuousMap.evalCLM ℝ z).intervalIntegral_comp_comm (μ := volume)
    ((reflectedFellerTimeOperator_continuous L hL D (D • F.curvatureMap)).intervalIntegrable 0 t)
  change (∫ r in 0..t, reflectedFellerTimeOperator L hL D r (D • F.curvatureMap) z) =
    (∫ r in 0..t, reflectedFellerTimeOperator L hL D r (D • F.curvatureMap)) z at hi
  change reflectedFellerTimeOperator L hL D t F.valueMap z - F.valueMap z =
    (∫ r in 0..t, reflectedFellerTimeOperator L hL D r (D • F.curvatureMap)) z at h
  rw [← hi] at h
  simpa only [map_smul, ContinuousMap.smul_apply, smul_eq_mul,
    intervalIntegral.integral_const_mul] using h

theorem ReflectedNeumannC2.feller_integral_apply_shift {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D) {s t : ℝ} (hst : s ≤ t) (z : Icc (0 : ℝ) L) :
    reflectedFellerTimeOperator L hL D (t - s) F.valueMap z - F.valueMap z =
      D * ∫ r in s..t, reflectedFellerTimeOperator L hL D (r - s) F.curvatureMap z := by
  rw [intervalIntegral.integral_comp_sub_right
    (fun r => reflectedFellerTimeOperator L hL D r F.curvatureMap z), sub_self]
  exact F.feller_integral_apply hL D hD (t - s) (sub_nonneg.mpr hst) z

end TimeTraps.Probability
