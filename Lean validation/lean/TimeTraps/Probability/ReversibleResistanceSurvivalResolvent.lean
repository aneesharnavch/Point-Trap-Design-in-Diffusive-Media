module

public import TimeTraps.Probability.ReversibleResistanceSurvival
public import TimeTraps.Probability.ReversibleResistanceMeanLifetime

@[expose] public section

/-! The paper's zero-resolvent expressed as the expected infinite time
integral of the actual physical survival weight. Product, path and time
integrability are conclusions of the proved finite mean lifetime. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reversibleResistanceSurvival_joint_integrable (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      reversibleResistanceAtomicSurvival D.medium x D.site κ p.1.toNNReal p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod brownianDyadicMeasure) := by
  let f := fun p : ℝ × (ℕ → ℝ) =>
    reversibleResistanceAtomicSurvival D.medium x D.site κ p.1.toNNReal p.2
  have hm : Measurable f :=
    (reversibleResistanceAtomicClock_jointlyMeasurable D.medium x D.site κ).neg.exp
  have hnneg : ∀ p, 0 ≤ f p := fun p =>
    (reversibleResistanceAtomicSurvival_bounds D.medium x D.site κ (fun i => (hκ i).le)
      p.1.toNNReal p.2).1.le
  have hlin : (∫⁻ p, ENNReal.ofReal (f p)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod brownianDyadicMeasure) =
      ENNReal.ofReal (D.resistanceMeanState hn κ hκ x) := by
    calc
      _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal
          (reversibleResistanceAtomicSurvival D.medium x D.site κ r.toNNReal ω)
            ∂brownianDyadicMeasure := lintegral_prod _ hm.ennreal_ofReal.aemeasurable
      _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal
          (reversibleResistanceMeanSurvival D.medium x D.site κ r.toNNReal) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro r _
        exact reversibleResistanceAtomicSurvival_lintegral D.medium x D.site κ
          (fun i => (hκ i).le) r.toNNReal
      _ = ∫⁻ p, reversibleResistanceAttainmentLifetimeValue D.medium x D.site κ p
          ∂exponentialKillingMeasure brownianDyadicMeasure :=
        (reversibleResistanceAttainmentLifetimeValue_mean_survival D.medium x D.site κ
          (fun i => (hκ i).le)).symm
      _ = _ := reversibleResistanceMeanLifetime_extended_mean hn hκ
        (D.resistanceMeanState_weak hn κ hκ) hx
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall hnneg)).mp (hlin ▸ ENNReal.ofReal_ne_top)

theorem reversibleResistanceSurvival_path_integrable_ae (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, IntegrableOn
      (fun r : ℝ => reversibleResistanceAtomicSurvival D.medium x D.site κ r.toNNReal ω)
        (Ioi (0 : ℝ)) :=
  (reversibleResistanceSurvival_joint_integrable D hn κ hκ hx).prod_left_ae

theorem reversibleResistanceSurvival_integral_integrable (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    Integrable (fun ω => ∫ r in Ioi (0 : ℝ),
      reversibleResistanceAtomicSurvival D.medium x D.site κ r.toNNReal ω) brownianDyadicMeasure :=
  (reversibleResistanceSurvival_joint_integrable D hn κ hκ hx).integral_prod_right

theorem reversibleResistanceMeanSurvival_integrable (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {x : ℝ}
    (hx : x ∈ Icc D.source.left D.source.right) :
    IntegrableOn (fun r : ℝ => reversibleResistanceMeanSurvival D.medium x D.site κ r.toNNReal)
      (Ioi (0 : ℝ)) :=
  (reversibleResistanceSurvival_joint_integrable D hn κ hκ hx).integral_prod_left

theorem reversibleResistanceMeanSurvival_integral {D : OrderedMedium n} (hn : 0 < n)
    {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ} (hu : WeakIntervalEquation D κ u)
    {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    (∫ r in Ioi (0 : ℝ), reversibleResistanceMeanSurvival D.medium x D.site κ r.toNNReal) = u x := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun r : ℝ => reversibleResistanceMeanSurvival D.medium x D.site κ r.toNNReal) :=
    Eventually.of_forall (fun r =>
      (reversibleResistanceMeanSurvival_bounds D.medium x D.site κ (fun i => (hκ i).le) r.toNNReal).1)
  have hux : 0 ≤ u x := by
    rw [← reversibleResistanceMeanLifetime_eq hn hκ hu hx]
    exact integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have h := (ofReal_integral_eq_lintegral_ofReal
    (reversibleResistanceMeanSurvival_integrable D hn κ hκ hx) hnonneg).trans
      ((reversibleResistanceAttainmentLifetimeValue_mean_survival D.medium x D.site κ
        (fun i => (hκ i).le)).symm.trans
          (reversibleResistanceMeanLifetime_extended_mean hn hκ hu hx))
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg), ENNReal.toReal_ofReal hux]
    using congrArg ENNReal.toReal h

noncomputable def reversibleResistanceSurvivalResolvent (A : IntervalMedium) (x : ℝ)
    (a κ : Fin n → ℝ) : ℝ :=
  ∫ ω, (∫ r in Ioi (0 : ℝ), reversibleResistanceAtomicSurvival A x a κ r.toNNReal ω)
    ∂brownianDyadicMeasure

theorem reversibleResistanceSurvivalResolvent_eq {D : OrderedMedium n} (hn : 0 < n)
    {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ} (hu : WeakIntervalEquation D κ u)
    {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    reversibleResistanceSurvivalResolvent D.medium x D.site κ = u x :=
  (integral_integral_swap (reversibleResistanceSurvival_joint_integrable D hn κ hκ hx)).symm.trans
    (reversibleResistanceMeanSurvival_integral hn hκ hu hx)

theorem reversibleResistanceSurvivalResolvent_weak_equation (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) :
    WeakIntervalEquation D κ (fun x => reversibleResistanceSurvivalResolvent D.medium x D.site κ) :=
  (D.resistanceMeanState_weak hn κ hκ).congr_state (fun _ hx =>
    (reversibleResistanceSurvivalResolvent_eq hn hκ (D.resistanceMeanState_weak hn κ hκ) hx).symm)

end TimeTraps.Probability
