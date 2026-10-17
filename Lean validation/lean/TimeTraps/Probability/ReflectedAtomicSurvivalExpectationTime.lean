module

public import TimeTraps.Probability.ReflectedAtomicSurvivalExpectation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Genuine finite-horizon integrability and Fubini for the literal
atomic survival process. The bound by one controls the finite product
measure and gives an integrable ordinary time integral. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicSurvival_time_intervalIntegrable (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (ω : ℕ → ℝ) :
    IntervalIntegrable (fun r : ℝ => reflectedAtomicSurvival L D x a κ r.toNNReal ω)
      volume 0 T.val := by
  have hm : Measurable (fun t : ℝ≥0 => reflectedAtomicSurvival L D x a κ t ω) :=
    Measurable.of_uncurry_right (f := fun t ω => reflectedAtomicSurvival L D x a κ t ω)
      (y := ω) (reflectedAtomicSurvival_jointlyMeasurable L D x a κ)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  apply (integrable_const (1 : ℝ)).mono' (hm.comp measurable_real_toNNReal).aestronglyMeasurable
  exact Eventually.of_forall (fun r => by
    change ‖reflectedAtomicSurvival L D x a κ r.toNNReal ω‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ r.toNNReal ω).1]
    exact (reflectedAtomicSurvival_bounds L hD x a κ hκ r.toNNReal ω).2)

theorem reflectedAtomicSurvival_time_joint_integrable (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => reflectedAtomicSurvival L D x a κ p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hW := (reflectedAtomicSurvival_jointlyMeasurable L D x a κ).comp hm
  apply (integrable_const (1 : ℝ)).mono' hW.aestronglyMeasurable
  exact Eventually.of_forall (fun p => by
    change ‖reflectedAtomicSurvival L D x a κ p.1.toNNReal p.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ p.1.toNNReal p.2).1]
    exact (reflectedAtomicSurvival_bounds L hD x a κ hκ p.1.toNNReal p.2).2)

theorem reflectedAtomicSurvival_time_integral_integrable (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x a κ r.toNNReal ω) brownianDyadicMeasure := by
  have h := (reflectedAtomicSurvival_time_joint_integrable L hD x a κ hκ T).integral_prod_right
  have he : (fun ω => ∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω) =
      fun ω => ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω := by
    funext ω
    exact intervalIntegral.integral_of_le T.coe_nonneg
  rw [he]
  exact h

theorem reflectedAtomicSurvival_mean_time_integral (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω)
      ∂brownianDyadicMeasure) =
      ∫ r in (0 : ℝ)..T.val, reflectedAtomicMeanSurvival L D x a κ r.toNNReal := by
  have h := integral_integral_swap
    (μ := volume.restrict (Ioc (0 : ℝ) T.val)) (ν := brownianDyadicMeasure)
    (f := fun (r : ℝ) (ω : ℕ → ℝ) => reflectedAtomicSurvival L D x a κ r.toNNReal ω)
    (reflectedAtomicSurvival_time_joint_integrable L hD x a κ hκ T)
  calc
    _ = ∫ ω, (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω)
        ∂brownianDyadicMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
    _ = ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicMeanSurvival L D x a κ r.toNNReal := h.symm
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

end TimeTraps.Probability
