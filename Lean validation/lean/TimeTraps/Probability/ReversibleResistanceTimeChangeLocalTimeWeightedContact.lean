module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeContact
public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeSubstitution

@[expose] public section

/-! Continuous time weights against the actual physical contact measure.
Integrability follows from clock transport and the reference Stieltjes
measure; the spatial weight is evaluated only at the supported level. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

theorem reversibleResistanceLocalTimeMeasure_continuous_integrable
    (A : IntervalMedium) (x a : ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (T : ℝ≥0) :
    IntegrableOn (fun t : ℝ => w t.toNNReal) (Ioc (0 : ℝ) T.val)
      (reversibleResistanceLocalTimeMeasure A x a ω) := by
  have hC : Continuous (fun s => reversibleResistanceClock A x s ω) :=
    (reflectedPositiveTimeChange_regular A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
          ω hω.continuous).1
  have hi : IntegrableOn (fun r : ℝ => w (reversibleResistanceClock A x r.toNNReal ω))
      (Ioc (reversibleResistanceInversePath A x 0 ω).val
        (reversibleResistanceInversePath A x T ω).val)
      (reflectedInteriorOccupationTimeMeasure (A.resistance x)
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * 1)) A.resistanceLength_pos
          (A.resistance a) ω) := by
    rw [reflectedInteriorOccupationTimeMeasure_eq_stieltjes]
    exact ((hw.comp hC).comp continuous_real_toNNReal).integrableOn_Ioc
  have hc (r : ℝ) : w (Real.toNNReal (reversibleResistanceClock A x r.toNNReal ω : ℝ)) =
      w (reversibleResistanceClock A x r.toNNReal ω) :=
    congrArg w (Real.toNNReal_coe (r := reversibleResistanceClock A x r.toNNReal ω))
  exact (reversibleResistanceLocalTimeMeasure_integrable_iff A x a hω 0 T
    (hw.comp continuous_real_toNNReal).measurable).mpr
      (hi.congr (Eventually.of_forall (fun r => (hc r).symm)))

theorem reversibleResistanceLocalTimeMeasure_weighted_contact
    (A : IntervalMedium) (x : ℝ) {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hr : reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a) ω)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun t => w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω))
      (Ioc (0 : ℝ) T.val) (reversibleResistanceLocalTimeMeasure A x a ω) ∧
      (∫ t in Ioc (0 : ℝ) T.val,
        w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω)
          ∂reversibleResistanceLocalTimeMeasure A x a ω) =
        g a * ∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal
          ∂reversibleResistanceLocalTimeMeasure A x a ω := by
  have hi := reversibleResistanceLocalTimeMeasure_continuous_integrable A x a hω w hw T
  have he : (fun t => w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω))
      =ᵐ[(reversibleResistanceLocalTimeMeasure A x a ω).restrict (Ioc (0 : ℝ) T.val)]
        (fun t => g a * w t.toNNReal) := by
    filter_upwards [ae_restrict_of_ae
      (reversibleResistanceLocalTimeMeasure_weight_ae A x ha hω hr g)] with t ht
    rw [ht, mul_comm]
  exact ⟨(hi.const_mul (g a)).congr he.symm,
    (integral_congr_ae he).trans (integral_const_mul _ _)⟩

end TimeTraps.Probability
