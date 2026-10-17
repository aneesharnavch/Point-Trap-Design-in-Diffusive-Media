module

public import TimeTraps.Probability.ReflectedAtomicWeightedValue
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Finite-time product integrability and Fubini for the actual
survival-weighted spatial value. Compact range bounds justify each
ordinary integral, including signed continuous spatial tests. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {ι : Type*} [Fintype ι] {V : ℝ → ℝ}

theorem reflectedAtomicWeightedValue_time_intervalIntegrable (hV : Continuous V)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (ω : ℕ → ℝ) :
    IntervalIntegrable (fun r : ℝ => reflectedAtomicWeightedValue V L D x a κ r.toNNReal ω)
      volume 0 T.val := by
  have hm : Measurable (fun t : ℝ≥0 => reflectedAtomicWeightedValue V L D x a κ t ω) :=
    Measurable.of_uncurry_right (f := fun t ω => reflectedAtomicWeightedValue V L D x a κ t ω)
      (y := ω) (reflectedAtomicWeightedValue_jointlyMeasurable hV L D x a κ)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  apply (integrable_const ‖reflectedAtomicValueMap hV L‖).mono'
    (hm.comp measurable_real_toNNReal).aestronglyMeasurable
  exact Eventually.of_forall (fun r => reflectedAtomicWeightedValue_bound hV L hL D hD x a κ hκ r.toNNReal ω)

theorem reflectedAtomicWeightedValue_time_joint_integrable (hV : Continuous V)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => reflectedAtomicWeightedValue V L D x a κ p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hW := (reflectedAtomicWeightedValue_jointlyMeasurable hV L D x a κ).comp hm
  apply (integrable_const ‖reflectedAtomicValueMap hV L‖).mono' hW.aestronglyMeasurable
  exact Eventually.of_forall (fun p => reflectedAtomicWeightedValue_bound hV L hL D hD x a κ hκ p.1.toNNReal p.2)

theorem reflectedAtomicWeightedValue_time_integral_integrable (hV : Continuous V)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val,
      reflectedAtomicWeightedValue V L D x a κ r.toNNReal ω) brownianDyadicMeasure := by
  have h := (reflectedAtomicWeightedValue_time_joint_integrable hV L hL D hD x a κ hκ T).integral_prod_right
  have he : (fun ω => ∫ r in (0 : ℝ)..T.val, reflectedAtomicWeightedValue V L D x a κ r.toNNReal ω) =
      fun ω => ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicWeightedValue V L D x a κ r.toNNReal ω := by
    funext ω
    exact intervalIntegral.integral_of_le T.coe_nonneg
  rw [he]
  exact h

theorem reflectedAtomicWeightedValue_mean_time_integral (hV : Continuous V)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val, reflectedAtomicWeightedValue V L D x a κ r.toNNReal ω)
      ∂brownianDyadicMeasure) =
      ∫ r in (0 : ℝ)..T.val, reflectedAtomicValueExpectation V L D x a κ r.toNNReal := by
  have h := integral_integral_swap
    (μ := volume.restrict (Ioc (0 : ℝ) T.val)) (ν := brownianDyadicMeasure)
    (f := fun (r : ℝ) (ω : ℕ → ℝ) => reflectedAtomicWeightedValue V L D x a κ r.toNNReal ω)
    (reflectedAtomicWeightedValue_time_joint_integrable hV L hL D hD x a κ hκ T)
  calc
    _ = ∫ ω, (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicWeightedValue V L D x a κ r.toNNReal ω)
        ∂brownianDyadicMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
    _ = ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicValueExpectation V L D x a κ r.toNNReal := h.symm
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

end TimeTraps.Probability
