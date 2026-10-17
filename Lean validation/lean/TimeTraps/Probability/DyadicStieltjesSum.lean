module

public import TimeTraps.Probability.BrownianAdaptedContinuousProcess
public import TimeTraps.Analysis.StieltjesLocalSupport
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Actual left dyadic Stieltjes sums. Each finite sum is exactly the
integral of its left-step function against the actual Stieltjes measure.
No probabilistic assumption is used. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def dyadicStieltjesSum (K : StieltjesFunction ℝ) (g : ℝ≥0 → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i : Fin (2 ^ n),
    (K (brownianDyadicGrid T n i.succ).val - K (brownianDyadicGrid T n i.castSucc).val) *
      g (brownianDyadicGrid T n i.castSucc)

theorem stieltjesIntervalIndicator_integrable (K : StieltjesFunction ℝ) (s t : ℝ≥0) :
    Integrable (brownianIntervalIndicator s t) K.measure := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact integrableOn_const (by rw [K.measure_Ioc]; exact ENNReal.ofReal_ne_top)

theorem stieltjesIntervalIndicator_integral (K : StieltjesFunction ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ r, brownianIntervalIndicator s t r ∂K.measure) = K t.val - K s.val := by
  rw [brownianIntervalIndicator, integral_indicator measurableSet_Ioc, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (K.mono hst)), smul_eq_mul, mul_one]

theorem dyadicStieltjesStep_integrable (K : StieltjesFunction ℝ) (g : ℝ≥0 → ℝ)
    (T : ℝ≥0) (n : ℕ) :
    Integrable (fun r => brownianSquareStepProcess (fun t (_ : Unit) => g t) T n (r, ()))
      K.measure := by
  change Integrable (fun r => ∑ i : Fin (2 ^ n),
    brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc)
      (brownianDyadicGrid T n i.succ) r * g (brownianDyadicGrid T n i.castSucc)) K.measure
  exact integrable_finsetSum Finset.univ (fun (i : Fin (2 ^ n)) _ =>
    (stieltjesIntervalIndicator_integrable K _ _).mul_const _)

theorem dyadicStieltjesStep_integral (K : StieltjesFunction ℝ) (g : ℝ≥0 → ℝ)
    (T : ℝ≥0) (n : ℕ) :
    (∫ r in Ioc (0 : ℝ) T.val,
      brownianSquareStepProcess (fun t (_ : Unit) => g t) T n (r, ()) ∂K.measure) =
      dyadicStieltjesSum K g T n := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr =>
    brownianSquareStepProcess_outside (fun t (_ : Unit) => g t) T n () hr)]
  change (∫ r, ∑ i : Fin (2 ^ n),
    brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc)
      (brownianDyadicGrid T n i.succ) r * g (brownianDyadicGrid T n i.castSucc) ∂K.measure) = _
  rw [integral_finsetSum _ (fun (i : Fin (2 ^ n)) _ =>
    (stieltjesIntervalIndicator_integrable K _ _).mul_const _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const,
    stieltjesIntervalIndicator_integral K (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i))]

end TimeTraps.Probability
