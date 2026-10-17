module

public import TimeTraps.Probability.ReversibleResistanceSurvivalData

@[expose] public section

/-! The actual physical survival weight has a continuous decreasing mean.
All domination follows from nonnegative atomic strengths, with no premise
that killing eventually occurs. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

noncomputable def reversibleResistanceMeanSurvival (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (T : ℝ≥0) : ℝ :=
  ∫ ω, reversibleResistanceAtomicSurvival A x a κ T ω ∂brownianDyadicMeasure

theorem reversibleResistanceAtomicSurvival_integrable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    Integrable (reversibleResistanceAtomicSurvival A x a κ T) brownianDyadicMeasure := by
  have hm := (reversibleResistanceAtomicSurvival_jointlyMeasurable A x a κ).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ω : ℕ → ℝ => (T, ω)))
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by
    change ‖reversibleResistanceAtomicSurvival A x a κ T ω‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (reversibleResistanceAtomicSurvival_bounds A x a κ hκ T ω).1]
    exact (reversibleResistanceAtomicSurvival_bounds A x a κ hκ T ω).2)

theorem reversibleResistanceMeanSurvival_bounds (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    0 ≤ reversibleResistanceMeanSurvival A x a κ T ∧
      reversibleResistanceMeanSurvival A x a κ T ≤ 1 := by
  constructor
  · exact integral_nonneg (fun ω => (reversibleResistanceAtomicSurvival_bounds A x a κ hκ T ω).1.le)
  · calc
      _ ≤ ∫ _ω, (1 : ℝ) ∂brownianDyadicMeasure :=
        integral_mono (reversibleResistanceAtomicSurvival_integrable A x a κ hκ T) (integrable_const 1)
          (fun ω => (reversibleResistanceAtomicSurvival_bounds A x a κ hκ T ω).2)
      _ = 1 := by simp

theorem reversibleResistanceMeanSurvival_zero (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    reversibleResistanceMeanSurvival A x a κ 0 = 1 := by
  have he : reversibleResistanceAtomicSurvival A x a κ 0 =ᵐ[brownianDyadicMeasure]
      (fun _ => 1) := by
    filter_upwards [reversibleResistanceAtomicHazard_paths A x a κ hκ] with ω hω
    exact hω.2.2.2.2.2
  change (∫ ω, reversibleResistanceAtomicSurvival A x a κ 0 ω ∂brownianDyadicMeasure) = 1
  rw [integral_congr_ae he]
  simp

theorem reversibleResistanceMeanSurvival_antitone (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    Antitone (reversibleResistanceMeanSurvival A x a κ) := by
  intro s t hst
  apply integral_mono_ae (reversibleResistanceAtomicSurvival_integrable A x a κ hκ t)
    (reversibleResistanceAtomicSurvival_integrable A x a κ hκ s)
  filter_upwards [reversibleResistanceAtomicHazard_paths A x a κ hκ] with ω hω
  exact hω.2.2.2.2.1 hst

theorem reversibleResistanceMeanSurvival_continuous (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    Continuous (reversibleResistanceMeanSurvival A x a κ) := by
  apply continuous_of_dominated
    (fun T => (reversibleResistanceAtomicSurvival_integrable A x a κ hκ T).aestronglyMeasurable)
    (bound := fun _ => (1 : ℝ))
  · intro T
    exact Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (reversibleResistanceAtomicSurvival_bounds A x a κ hκ T ω).1]
      exact (reversibleResistanceAtomicSurvival_bounds A x a κ hκ T ω).2)
  · exact integrable_const 1
  · filter_upwards [reversibleResistanceAtomicHazard_paths A x a κ hκ] with ω hω
    exact hω.2.2.2.1

theorem reversibleResistanceAtomicSurvival_lintegral (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (reversibleResistanceAtomicSurvival A x a κ T ω) ∂brownianDyadicMeasure) =
      ENNReal.ofReal (reversibleResistanceMeanSurvival A x a κ T) :=
  (ofReal_integral_eq_lintegral_ofReal
    (reversibleResistanceAtomicSurvival_integrable A x a κ hκ T)
    (Eventually.of_forall (fun ω => (reversibleResistanceAtomicSurvival_bounds A x a κ hκ T ω).1.le))).symm

end TimeTraps.Probability
