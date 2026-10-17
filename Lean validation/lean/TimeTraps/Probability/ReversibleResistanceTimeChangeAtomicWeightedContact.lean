module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeAtomicMeasure
public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeWeightedContact

@[expose] public section

/-! Exact finite-atom contact cancellation for the physical diffusion.
The original strengths multiply the original physical site values, with
continuous time weights and no regularity assumption on the spatial test. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reversibleResistanceAtomicTimeMeasure_weighted_contact
    (A : IntervalMedium) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (ha : ∀ i, a i ∈ Ioo A.source.left A.source.right)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hr : ∀ i, reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance (a i)) ω)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun t => w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω))
      (Ioc (0 : ℝ) T.val) (reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) ∧
      (∫ t in Ioc (0 : ℝ) T.val,
        w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω)
          ∂reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) =
        ∑ i, κ i * g (a i) * ∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal
          ∂reversibleResistanceLocalTimeMeasure A x (a i) ω := by
  let μ : ι → Measure ℝ := fun i => reversibleResistanceLocalTimeMeasure A x (a i) ω
  let f : ℝ → ℝ := fun t => w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω)
  have hi (i : ι) := reversibleResistanceLocalTimeMeasure_weighted_contact
    A x (ha i) hω (hr i) w hw g T
  have hrestrict : (reversibleResistanceAtomicTimeMeasure A x a κ hκ ω).restrict
      (Ioc (0 : ℝ) T.val) = ∑ i, Real.toNNReal (κ i) • (μ i).restrict (Ioc (0 : ℝ) T.val) := by
    rw [reversibleResistanceAtomicTimeMeasure_eq_sum]
    change (Measure.restrictₗ (Ioc (0 : ℝ) T.val)) (∑ i, Real.toNNReal (κ i) • μ i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => Measure.restrict_smul _ _ _)
  have hfi (i : ι) : Integrable f (Real.toNNReal (κ i) • (μ i).restrict (Ioc (0 : ℝ) T.val)) :=
    (hi i).1.smul_measure_nnreal
  constructor
  · change Integrable f _
    rw [hrestrict]
    exact integrable_finsetSum_measure.mpr (fun i _ => hfi i)
  · change (∫ t, f t ∂(reversibleResistanceAtomicTimeMeasure A x a κ hκ ω).restrict
      (Ioc (0 : ℝ) T.val)) = _
    rw [hrestrict, integral_finsetSum_measure (fun i _ => hfi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_nnreal_measure]
    change (Real.toNNReal (κ i) : ℝ) * (∫ t in Ioc (0 : ℝ) T.val, f t ∂μ i) = _
    rw [Real.coe_toNNReal _ (hκ i)]
    have he : (∫ t in Ioc (0 : ℝ) T.val, f t ∂μ i) =
        g (a i) * ∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal ∂μ i := (hi i).2
    rw [he]
    ring

theorem reversibleResistanceAtomicTimeMeasure_weighted_contact_ae
    (A : IntervalMedium) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (ha : ∀ i, a i ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ w : ℝ≥0 → ℝ, Continuous w →
      ∀ (g : ℝ → ℝ) (T : ℝ≥0),
      IntegrableOn (fun t => w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω))
        (Ioc (0 : ℝ) T.val) (reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) ∧
        (∫ t in Ioc (0 : ℝ) T.val,
          w t.toNNReal * g (reversibleResistancePath A x t.toNNReal ω)
            ∂reversibleResistanceAtomicTimeMeasure A x a κ hκ ω) =
          ∑ i, κ i * g (a i) * ∫ t in Ioc (0 : ℝ) T.val, w t.toNNReal
            ∂reversibleResistanceLocalTimeMeasure A x (a i) ω := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
        A.resistanceLength (A.resistance (a i)) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae (A.resistance x)
      (Real.sqrt (2 * 1)) A.resistanceLength (A.resistance (a i)))
  filter_upwards [brownianDyadic_regular_ae, hall] with ω hω hr
  exact fun w hw g T => reversibleResistanceAtomicTimeMeasure_weighted_contact A x a κ hκ ha hω hr w hw g T

end TimeTraps.Probability
