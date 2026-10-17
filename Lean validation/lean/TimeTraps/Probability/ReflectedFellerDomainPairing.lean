module

public import TimeTraps.Probability.ReflectedFellerNeumannGenerator
public import TimeTraps.Probability.ReflectedGaussianBalance
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section

/-! Actual uniform integral pairings for the Feller generator converse.
The pairing is bounded on C([0,L]); reversibility is the independently
proved symmetry of the actual reflected transition law. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedFellerMean_uniform (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerMean L hL f = ∫ x, reflectedFellerExtension L hL f x ∂reflectedUniformLaw L hL := by
  rw [reflectedFellerMean_apply, reflectedUniformLaw, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hL.le, smul_eq_mul,
    intervalIntegral.integral_of_le hL.le, integral_Icc_eq_integral_Ioc]

def reflectedFellerPairing (L : ℝ) (hL : 0 < L) (f : C(Icc (0 : ℝ) L, ℝ)) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] ℝ :=
  (reflectedFellerMean L hL).comp (ContinuousLinearMap.mul ℝ C(Icc (0 : ℝ) L, ℝ) f)

theorem reflectedFellerPairing_apply (L : ℝ) (hL : 0 < L)
    (f g : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerPairing L hL f g = reflectedFellerMean L hL (f * g) := rfl

theorem reflectedFellerPairing_uniform (L : ℝ) (hL : 0 < L)
    (f g : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerPairing L hL f g = ∫ x, reflectedFellerExtension L hL f x *
      reflectedFellerExtension L hL g x ∂reflectedUniformLaw L hL :=
  reflectedFellerMean_uniform L hL (f * g)

theorem reflectedFellerPairing_comm (L : ℝ) (hL : 0 < L)
    (f g : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerPairing L hL f g = reflectedFellerPairing L hL g f := by
  rw [reflectedFellerPairing_apply, reflectedFellerPairing_apply, mul_comm]

theorem reflectedFellerPairing_balance (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f g : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerPairing L hL f (reflectedFellerOperator L hL v g) =
      reflectedFellerPairing L hL g (reflectedFellerOperator L hL v f) := by
  rw [reflectedFellerPairing_uniform, reflectedFellerPairing_uniform]
  exact reflectedFellerOperator_uniform_balance L hL v f g

theorem reflectedFellerPairing_cosine_time (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (n : ℕ) (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    reflectedFellerPairing L hL (neumannCosine L n) (reflectedFellerTimeOperator L hL D t f) =
      Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t) *
        reflectedFellerPairing L hL (neumannCosine L n) f := by
  change reflectedFellerPairing L hL (neumannCosine L n)
    (reflectedFellerOperator L hL (Real.toNNReal (2 * D * t)) f) = _
  rw [reflectedFellerPairing_balance, reflectedFellerOperator_cosine_time L hL D hD n t ht,
    map_smul, smul_eq_mul, reflectedFellerPairing_comm L hL f]

end TimeTraps.Probability

end
