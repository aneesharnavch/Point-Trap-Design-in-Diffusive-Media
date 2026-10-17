module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeMeasure

@[expose] public section

/-! Exact transport of fixed-level time integrals by the clock. This
acts on the actual contact measures, including their restrictions to a
finite physical interval, and transports integrability in both directions. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

theorem reversibleResistanceLocalTimeMeasure_restrict (A : IntervalMedium) (x a : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (S T : ℝ≥0) :
    (reversibleResistanceLocalTimeMeasure A x a ω).restrict (Ioc S.val T.val) =
      ((reflectedInteriorOccupationTimeMeasure (A.resistance x)
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * 1)) A.resistanceLength_pos
          (A.resistance a) ω).restrict
            (Ioc (reversibleResistanceInversePath A x S ω).val
              (reversibleResistanceInversePath A x T ω).val)).map
                (fun r => (reversibleResistanceClock A x r.toNNReal ω : ℝ)) := by
  rw [reversibleResistanceLocalTimeMeasure,
    Measure.restrict_map (reversibleResistanceClock_real_measurable A x ω) measurableSet_Ioc,
    reversibleResistanceClock_preimage_Ioc A x hω]

theorem reversibleResistanceLocalTimeMeasure_integral_substitution
    (A : IntervalMedium) (x a : ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (S T : ℝ≥0) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ t in Ioc S.val T.val, g t ∂reversibleResistanceLocalTimeMeasure A x a ω) =
      ∫ s in Ioc (reversibleResistanceInversePath A x S ω).val
          (reversibleResistanceInversePath A x T ω).val,
        g (reversibleResistanceClock A x s.toNNReal ω : ℝ)
          ∂reflectedInteriorOccupationTimeMeasure (A.resistance x)
            (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * 1)) A.resistanceLength_pos
              (A.resistance a) ω := by
  rw [reversibleResistanceLocalTimeMeasure_restrict A x a hω S T]
  exact integral_map (reversibleResistanceClock_real_measurable A x ω).aemeasurable
    hg.aestronglyMeasurable

theorem reversibleResistanceLocalTimeMeasure_integrable_iff
    (A : IntervalMedium) (x a : ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (S T : ℝ≥0) {g : ℝ → ℝ} (hg : Measurable g) :
    IntegrableOn g (Ioc S.val T.val) (reversibleResistanceLocalTimeMeasure A x a ω) ↔
      IntegrableOn (fun s => g (reversibleResistanceClock A x s.toNNReal ω : ℝ))
        (Ioc (reversibleResistanceInversePath A x S ω).val
          (reversibleResistanceInversePath A x T ω).val)
        (reflectedInteriorOccupationTimeMeasure (A.resistance x)
          (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * 1)) A.resistanceLength_pos
            (A.resistance a) ω) := by
  change Integrable g ((reversibleResistanceLocalTimeMeasure A x a ω).restrict (Ioc S.val T.val)) ↔ _
  rw [reversibleResistanceLocalTimeMeasure_restrict A x a hω S T]
  exact integrable_map_measure hg.aestronglyMeasurable
    (reversibleResistanceClock_real_measurable A x ω).aemeasurable

end TimeTraps.Probability
