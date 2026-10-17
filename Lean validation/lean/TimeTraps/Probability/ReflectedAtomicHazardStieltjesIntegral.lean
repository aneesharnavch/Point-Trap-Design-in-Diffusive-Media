module

public import TimeTraps.Probability.ReflectedAtomicHazardStieltjes
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! Weighted contact cancellation for the actual atomic hazard measure.
The time weight is continuous and may be unbounded outside the finite
horizon. The spatial factor is arbitrary: support of each occupation
measure makes it equal almost everywhere to its value at that contact. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reflectedInteriorOccupationTimeMeasure_weighted_contact
    {x σ L a : ℝ} {ω : ℕ → ℝ} (hσ : 0 < σ) (hL : 0 < L)
    (ha : a ∈ Ioo 0 L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun r => w r.toNNReal * g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω)))
      (Ioc (0 : ℝ) T.val) (reflectedInteriorOccupationTimeMeasure x hσ hL a ω) ∧
    (∫ r in Ioc (0 : ℝ) T.val,
      w r.toNNReal * g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω))
      ∂reflectedInteriorOccupationTimeMeasure x hσ hL a ω) =
      g a * ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂reflectedInteriorOccupationTimeMeasure x hσ hL a ω := by
  have hi : IntegrableOn (fun r : ℝ => w r.toNNReal) (Ioc (0 : ℝ) T.val)
      (reflectedInteriorOccupationTimeMeasure x hσ hL a ω) := by
    rw [reflectedInteriorOccupationTimeMeasure_eq_stieltjes]
    exact (hw.comp continuous_real_toNNReal).integrableOn_Ioc
  have he : (fun r : ℝ => w r.toNNReal *
      g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω))) =ᵐ[
      (reflectedInteriorOccupationTimeMeasure x hσ hL a ω).restrict (Ioc (0 : ℝ) T.val)]
        (fun r => g a * w r.toNNReal) := by
    filter_upwards [ae_restrict_of_ae
      (reflectedInteriorOccupationTimeMeasure_weight_ae hσ hL ha hω g)] with r hr
    rw [hr, mul_comm]
  exact ⟨(hi.const_mul (g a)).congr he.symm,
    (integral_congr_ae he).trans (integral_const_mul _ _)⟩

theorem reflectedAtomicHazardTimeMeasure_weighted_contact
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (ha : ∀ i, a i ∈ Ioo 0 L) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun r => w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))
      (Ioc (0 : ℝ) T.val) (reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) ∧
    (∫ r in Ioc (0 : ℝ) T.val,
      w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
      ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) =
      ∑ i, κ i * g (a i) * ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂reflectedInteriorOccupationTimeMeasure x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω := by
  let μ : ι → Measure ℝ := fun i => reflectedInteriorOccupationTimeMeasure x
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω
  let f : ℝ → ℝ := fun r => w r.toNNReal *
    g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
  have hi (i : ι) := reflectedInteriorOccupationTimeMeasure_weighted_contact
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (ha i) (hω i) w hw g T
  have hr : (reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω).restrict (Ioc (0 : ℝ) T.val) =
      ∑ i, Real.toNNReal (κ i) • (μ i).restrict (Ioc (0 : ℝ) T.val) := by
    rw [reflectedAtomicHazardTimeMeasure_eq_sum]
    change (Measure.restrictₗ (Ioc (0 : ℝ) T.val)) (∑ i, Real.toNNReal (κ i) • μ i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => Measure.restrict_smul _ _ _)
  have hfi (i : ι) : Integrable f (Real.toNNReal (κ i) • (μ i).restrict (Ioc (0 : ℝ) T.val)) :=
    (hi i).1.smul_measure_nnreal
  constructor
  · change Integrable f _
    rw [hr]
    exact integrable_finsetSum_measure.mpr (fun i _ => hfi i)
  · change (∫ r, f r ∂(reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω).restrict
      (Ioc (0 : ℝ) T.val)) = _
    rw [hr, integral_finsetSum_measure (fun i _ => hfi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_nnreal_measure]
    change (Real.toNNReal (κ i) : ℝ) * (∫ r in Ioc (0 : ℝ) T.val, f r ∂μ i) = _
    rw [Real.coe_toNNReal _ (hκ i)]
    have he : (∫ r in Ioc (0 : ℝ) T.val, f r ∂μ i) =
        g (a i) * ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal ∂μ i := (hi i).2
    rw [he]
    ring

theorem reflectedAtomicHazardTimeMeasure_weighted_contact_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (ha : ∀ i, a i ∈ Ioo 0 L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ w : ℝ≥0 → ℝ, Continuous w →
      ∀ g : ℝ → ℝ, ∀ T : ℝ≥0,
      IntegrableOn (fun r => w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))
        (Ioc (0 : ℝ) T.val) (reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) ∧
      (∫ r in Ioc (0 : ℝ) T.val,
        w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
        ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) =
        ∑ i, κ i * g (a i) * ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
          ∂reflectedInteriorOccupationTimeMeasure x
            (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [hall] with ω hω
  exact fun w hw g T =>
    reflectedAtomicHazardTimeMeasure_weighted_contact L hL D hD x a κ hκ ha hω w hw g T

end TimeTraps.Probability
