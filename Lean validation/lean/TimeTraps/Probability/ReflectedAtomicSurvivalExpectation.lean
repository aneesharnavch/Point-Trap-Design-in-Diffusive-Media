module

public import TimeTraps.Probability.ReflectedAtomicHazardPaths
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! The mean of the actual atomic survival process. Its bounds,
monotonicity, and continuity follow from the proved path properties and
bounded dominated convergence; no eventual killing is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {ι : Type*} [Fintype ι]

noncomputable def reflectedAtomicMeanSurvival (L D x : ℝ) (a κ : ι → ℝ) (T : ℝ≥0) : ℝ :=
  ∫ ω, reflectedAtomicSurvival L D x a κ T ω ∂brownianDyadicMeasure

theorem reflectedAtomicSurvival_integrable (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    Integrable (reflectedAtomicSurvival L D x a κ T) brownianDyadicMeasure := by
  have hm := (reflectedAtomicSurvival_jointlyMeasurable L D x a κ).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ω : ℕ → ℝ => (T, ω)))
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by
    change ‖reflectedAtomicSurvival L D x a κ T ω‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ T ω).1]
    exact (reflectedAtomicSurvival_bounds L hD x a κ hκ T ω).2)

theorem reflectedAtomicMeanSurvival_bounds (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    0 ≤ reflectedAtomicMeanSurvival L D x a κ T ∧ reflectedAtomicMeanSurvival L D x a κ T ≤ 1 := by
  constructor
  · exact integral_nonneg (fun ω => (reflectedAtomicSurvival_bounds L hD x a κ hκ T ω).1.le)
  · calc
      _ ≤ ∫ _ω, (1 : ℝ) ∂brownianDyadicMeasure :=
        integral_mono (reflectedAtomicSurvival_integrable L hD x a κ hκ T) (integrable_const 1)
          (fun ω => (reflectedAtomicSurvival_bounds L hD x a κ hκ T ω).2)
      _ = 1 := by simp

theorem reflectedAtomicMeanSurvival_zero (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    reflectedAtomicMeanSurvival L D x a κ 0 = 1 := by
  have he : reflectedAtomicSurvival L D x a κ 0 =ᵐ[brownianDyadicMeasure] (fun _ => 1) := by
    filter_upwards [reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω
    exact hω.2.2.2.2.2
  change (∫ ω, reflectedAtomicSurvival L D x a κ 0 ω ∂brownianDyadicMeasure) = 1
  rw [integral_congr_ae he]
  simp

theorem reflectedAtomicMeanSurvival_antitone (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    Antitone (reflectedAtomicMeanSurvival L D x a κ) := by
  intro s t hst
  apply integral_mono_ae (reflectedAtomicSurvival_integrable L hD x a κ hκ t)
    (reflectedAtomicSurvival_integrable L hD x a κ hκ s)
  filter_upwards [reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω
  exact hω.2.2.2.2.1 hst

theorem reflectedAtomicMeanSurvival_continuous (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    Continuous (reflectedAtomicMeanSurvival L D x a κ) := by
  apply continuous_of_dominated
    (fun T => (reflectedAtomicSurvival_integrable L hD x a κ hκ T).aestronglyMeasurable)
    (bound := fun _ => (1 : ℝ))
  · intro T
    exact Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ T ω).1]
      exact (reflectedAtomicSurvival_bounds L hD x a κ hκ T ω).2)
  · exact integrable_const 1
  · filter_upwards [reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω
    exact hω.2.2.2.1

end TimeTraps.Probability
