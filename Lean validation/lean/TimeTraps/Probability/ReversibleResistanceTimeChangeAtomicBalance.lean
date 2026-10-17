module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeAtomicMeasure

@[expose] public section

/-! Exact finite-horizon survival balance for the actual physical
atomic hazard. Integrability is transported through the contact measure;
the result does not assume any infinite-horizon survival limit. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reversibleResistanceAtomicSurvival_real_measurable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (ω : ℕ → ℝ) :
    Measurable (fun t : ℝ => reversibleResistanceAtomicSurvival A x a κ t.toNNReal ω) := by
  let q : ℝ → ℝ≥0 × (ℕ → ℝ) := fun t => (t.toNNReal, ω)
  have hq : Measurable q := continuous_real_toNNReal.measurable.prodMk measurable_const
  have hm := (reversibleResistanceAtomicSurvival_jointlyMeasurable A x a κ).comp hq
  exact hm

theorem reversibleResistanceAtomic_survival_balance (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω)
    (hr : ∀ i, reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance (a i)) ω) (T : ℝ≥0) :
    IntegrableOn (fun t => reversibleResistanceAtomicSurvival A x a κ t.toNNReal ω)
      (Ioc (0 : ℝ) T.val) (reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) ∧
      (∫ t in Ioc (0 : ℝ) T.val, reversibleResistanceAtomicSurvival A x a κ t.toNNReal ω
        ∂reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) =
        1 - reversibleResistanceAtomicSurvival A x a κ T ω := by
  let ν := (reflectedAtomicHazardTimeMeasure A.resistanceLength A.resistanceLength_pos 1 zero_lt_one
    (A.resistance x) (fun i => A.resistance (a i)) κ hκ ω).restrict
      (Ioc (0 : ℝ) (reversibleResistanceInversePath A x T ω).val)
  let C : ℝ → ℝ := fun r => (reversibleResistanceClock A x r.toNNReal ω : ℝ)
  let W : ℝ → ℝ := fun t => reversibleResistanceAtomicSurvival A x a κ t.toNNReal ω
  have hC : Measurable C := reversibleResistanceClock_real_measurable A x ω
  have hW : Measurable W := reversibleResistanceAtomicSurvival_real_measurable A x a κ ω
  have hmeasure : (reversibleResistanceAtomicTimeMeasure A x a κ hκ ω).restrict
      (Ioc (0 : ℝ) T.val) = ν.map C := by
    have he := reversibleResistanceAtomicTimeMeasure_restrict A x a κ hκ hω 0 T
    rw [reversibleResistanceInversePath_zero] at he
    exact he
  have hcomp (r : ℝ) : W (C r) = reflectedAtomicSurvival A.resistanceLength 1 (A.resistance x)
      (fun i => A.resistance (a i)) κ r.toNNReal ω := by
    have hn := Real.toNNReal_coe (r := reversibleResistanceClock A x r.toNNReal ω)
    exact (congrArg (fun t => reversibleResistanceAtomicSurvival A x a κ t ω) hn).trans
      (reversibleResistanceAtomicSurvival_clock A x a κ hω r.toNNReal)
  have hI : Integrable (fun r => W (C r)) ν :=
    (reflectedAtomicHazard_survival_integrable A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) (fun i => A.resistance (a i)) κ hκ hr
        (reversibleResistanceInversePath A x T ω)).congr
          (Eventually.of_forall (fun r => (hcomp r).symm))
  refine ⟨?_, ?_⟩
  · change Integrable W ((reversibleResistanceAtomicTimeMeasure A x a κ hκ ω).restrict
      (Ioc (0 : ℝ) T.val))
    rw [hmeasure]
    exact (integrable_map_measure hW.aestronglyMeasurable hC.aemeasurable).mpr hI
  · change (∫ t, W t ∂(reversibleResistanceAtomicTimeMeasure A x a κ hκ ω).restrict
      (Ioc (0 : ℝ) T.val)) = _
    rw [hmeasure]
    calc
      _ = ∫ r, W (C r) ∂ν := integral_map hC.aemeasurable hW.aestronglyMeasurable
      _ = ∫ r, reflectedAtomicSurvival A.resistanceLength 1 (A.resistance x)
          (fun i => A.resistance (a i)) κ r.toNNReal ω ∂ν :=
        integral_congr_ae (Eventually.of_forall hcomp)
      _ = _ := reflectedAtomicHazard_survival_balance A.resistanceLength A.resistanceLength_pos
        1 zero_lt_one (A.resistance x) (fun i => A.resistance (a i)) κ hκ hr
          (reversibleResistanceInversePath A x T ω)

theorem reversibleResistanceAtomic_survival_balance_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      IntegrableOn (fun t => reversibleResistanceAtomicSurvival A x a κ t.toNNReal ω)
        (Ioc (0 : ℝ) T.val) (reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) ∧
        (∫ t in Ioc (0 : ℝ) T.val, reversibleResistanceAtomicSurvival A x a κ t.toNNReal ω
          ∂reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) =
          1 - reversibleResistanceAtomicSurvival A x a κ T ω := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
        A.resistanceLength (A.resistance (a i)) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae (A.resistance x)
      (Real.sqrt (2 * 1)) A.resistanceLength (A.resistance (a i)))
  filter_upwards [brownianDyadic_regular_ae, hall] with ω hω hr
  exact fun T => reversibleResistanceAtomic_survival_balance A x a κ hκ hω hr T

end TimeTraps.Probability
