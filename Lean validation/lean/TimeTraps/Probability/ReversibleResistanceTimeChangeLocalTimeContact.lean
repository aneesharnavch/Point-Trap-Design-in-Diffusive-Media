module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeMeasure

@[expose] public section

/-! Exact atomic contact integrals for the physical process. Each
fixed-level event works for every finite horizon and every spatial
weight, including weights with no regularity assumption. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

theorem reversibleResistanceLocalTimeMeasure_weight_ae (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hr : reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a) ω) (g : ℝ → ℝ) :
    (fun t => g (reversibleResistancePath A x t.toNNReal ω))
      =ᵐ[reversibleResistanceLocalTimeMeasure A x a ω] (fun _ => g a) := by
  filter_upwards [reversibleResistanceLocalTimeMeasure_contact A x ha hω hr] with t ht
  exact congrArg g ht.2

theorem reversibleResistanceLocalTimeMeasure_weight_integral (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hr : reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a) ω) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun t => g (reversibleResistancePath A x t.toNNReal ω))
      (Ioc (0 : ℝ) T.val) (reversibleResistanceLocalTimeMeasure A x a ω) ∧
      (∫ t in Ioc (0 : ℝ) T.val, g (reversibleResistancePath A x t.toNNReal ω)
        ∂reversibleResistanceLocalTimeMeasure A x a ω) =
        g a * reversibleResistanceLocalTime A x a T ω := by
  have : IsFiniteMeasure ((reversibleResistanceLocalTimeMeasure A x a ω).restrict
      (Ioc (0 : ℝ) T.val)) :=
    ⟨by rw [Measure.restrict_apply_univ, reversibleResistanceLocalTimeMeasure_mass A x a hω hr]
        exact ENNReal.ofReal_lt_top⟩
  have he : (fun t => g (reversibleResistancePath A x t.toNNReal ω))
      =ᵐ[(reversibleResistanceLocalTimeMeasure A x a ω).restrict (Ioc (0 : ℝ) T.val)]
        (fun _ => g a) :=
    ae_restrict_of_ae (reversibleResistanceLocalTimeMeasure_weight_ae A x ha hω hr g)
  refine ⟨(integrable_const (g a)).congr he.symm, ?_⟩
  calc
    _ = ∫ _ in Ioc (0 : ℝ) T.val, g a ∂reversibleResistanceLocalTimeMeasure A x a ω :=
      integral_congr_ae he
    _ = g a * reversibleResistanceLocalTime A x a T ω := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def,
        reversibleResistanceLocalTimeMeasure_mass A x a hω hr,
        ENNReal.toReal_ofReal (reversibleResistanceLocalTime_nonneg A x a T ω), mul_comm]

theorem reversibleResistanceLocalTimeMeasure_weight_integral_ae
    (A : IntervalMedium) (x : ℝ) {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (g : ℝ → ℝ) (T : ℝ≥0),
      IntegrableOn (fun t => g (reversibleResistancePath A x t.toNNReal ω))
        (Ioc (0 : ℝ) T.val) (reversibleResistanceLocalTimeMeasure A x a ω) ∧
        (∫ t in Ioc (0 : ℝ) T.val, g (reversibleResistancePath A x t.toNNReal ω)
          ∂reversibleResistanceLocalTimeMeasure A x a ω) =
          g a * reversibleResistanceLocalTime A x a T ω := by
  filter_upwards [brownianDyadic_regular_ae,
    reflectedInteriorLocalTimeRegular_ae (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a)] with ω hω hr
  exact fun g T => reversibleResistanceLocalTimeMeasure_weight_integral A x ha hω hr g T

end TimeTraps.Probability
