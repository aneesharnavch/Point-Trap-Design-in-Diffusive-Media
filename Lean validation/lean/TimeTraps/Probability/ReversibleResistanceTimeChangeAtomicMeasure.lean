module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeAtomicHazardPaths
public import TimeTraps.Probability.ReflectedAtomicHazardBalance

@[expose] public section

/-! The physical atomic hazard measure is transported by the actual
clock. It equals the finite sum of the physical contact measures with
the original nonnegative trap strengths. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

noncomputable def reversibleResistanceAtomicTimeMeasure (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) : Measure ℝ :=
  (reflectedAtomicHazardTimeMeasure A.resistanceLength A.resistanceLength_pos 1 zero_lt_one
    (A.resistance x) (fun i => A.resistance (a i)) κ hκ ω).map
      (fun r => (reversibleResistanceClock A x r.toNNReal ω : ℝ))

theorem reversibleResistanceAtomicTimeMeasure_eq_sum (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) :
    reversibleResistanceAtomicTimeMeasure A x a κ hκ ω =
      ∑ i, Real.toNNReal (κ i) • reversibleResistanceLocalTimeMeasure A x (a i) ω := by
  classical
  let C : ℝ → ℝ := fun r => (reversibleResistanceClock A x r.toNNReal ω : ℝ)
  have hC : Measurable C := reversibleResistanceClock_real_measurable A x ω
  have hm (s : Finset ι) (ν : ι → Measure ℝ) :
      (∑ i ∈ s, ν i).map C = ∑ i ∈ s, (ν i).map C := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Measure.map_zero]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Measure.map_add _ _ hC, ih, Finset.sum_insert hi]
  rw [reversibleResistanceAtomicTimeMeasure, reflectedAtomicHazardTimeMeasure_eq_sum, hm]
  apply Finset.sum_congr rfl
  intro i _
  exact Measure.map_smul _ _ _

theorem reversibleResistanceAtomicTimeMeasure_restrict (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω) (S T : ℝ≥0) :
    (reversibleResistanceAtomicTimeMeasure A x a κ hκ ω).restrict (Ioc S.val T.val) =
      ((reflectedAtomicHazardTimeMeasure A.resistanceLength A.resistanceLength_pos 1 zero_lt_one
        (A.resistance x) (fun i => A.resistance (a i)) κ hκ ω).restrict
          (Ioc (reversibleResistanceInversePath A x S ω).val
            (reversibleResistanceInversePath A x T ω).val)).map
              (fun r => (reversibleResistanceClock A x r.toNNReal ω : ℝ)) := by
  rw [reversibleResistanceAtomicTimeMeasure,
    Measure.restrict_map (reversibleResistanceClock_real_measurable A x ω) measurableSet_Ioc,
    reversibleResistanceClock_preimage_Ioc A x hω]

theorem reversibleResistanceAtomicTimeMeasure_Ioc (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω)
    (hr : ∀ i, reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance (a i)) ω) (S T : ℝ≥0) :
    reversibleResistanceAtomicTimeMeasure A x a κ hκ ω (Ioc S.val T.val) =
      ENNReal.ofReal (reversibleResistanceAtomicHazard A x a κ T ω -
        reversibleResistanceAtomicHazard A x a κ S ω) := by
  rw [reversibleResistanceAtomicTimeMeasure,
    Measure.map_apply (reversibleResistanceClock_real_measurable A x ω) measurableSet_Ioc,
    reversibleResistanceClock_preimage_Ioc A x hω]
  have hi := reflectedAtomicHazardTimeMeasure_Ioc A.resistanceLength A.resistanceLength_pos
    1 zero_lt_one (A.resistance x) (fun i => A.resistance (a i)) κ hκ hr
      (reversibleResistanceInversePath A x S ω).val (reversibleResistanceInversePath A x T ω).val
  exact hi.trans (congrArg ENNReal.ofReal (congrArg₂ (fun u v : ℝ => u - v)
    (congrArg (fun t => reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
      (fun i => A.resistance (a i)) κ t ω)
        (Real.toNNReal_coe (r := reversibleResistanceInversePath A x T ω)))
    (congrArg (fun t => reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
      (fun i => A.resistance (a i)) κ t ω)
        (Real.toNNReal_coe (r := reversibleResistanceInversePath A x S ω)))))

end TimeTraps.Probability
