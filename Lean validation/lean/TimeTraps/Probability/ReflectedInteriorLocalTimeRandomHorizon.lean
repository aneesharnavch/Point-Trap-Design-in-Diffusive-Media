module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeMaximal
public import TimeTraps.Probability.ReflectedAtomicHazardData

@[expose] public section

/-! Spatial local-time increments remain L2-small at arbitrary measurable
bounded random horizons. The estimate comes from a common all-time event,
so no fixed-time null set is substituted at a random time. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorOccupation_level_compact_bound_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |reflectedInteriorOccupationCoefficient x σ L a.val t ω -
        reflectedInteriorOccupationCoefficient x σ L b.val t ω| ≤
      reflectedInteriorLevelError L hL x hσ T a b ω / σ ^ 2 := by
  filter_upwards [reflectedInteriorLevelError_bound_ae L hL x hσ T a b] with ω hω t ht
  rw [reflectedInteriorOccupationCoefficient, reflectedInteriorOccupationCoefficient,
    ← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hσ)]
  exact div_le_div_of_nonneg_right (hω t ht) (sq_nonneg σ)

theorem reflectedInteriorOccupation_random_difference_memLp (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L)
    (τ : (ℕ → ℝ) → ℝ≥0) (hτ : Measurable τ) (hτT : ∀ᵐ ω ∂brownianDyadicMeasure, τ ω ≤ T) :
    MemLp (fun ω => reflectedInteriorOccupationCoefficient x σ L a.val (τ ω) ω -
      reflectedInteriorOccupationCoefficient x σ L b.val (τ ω) ω) 2 brownianDyadicMeasure := by
  let q : (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) := fun ω => (τ ω, ω)
  have hq : Measurable q := hτ.prodMk measurable_id
  have haM := (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable x σ L a.val).comp hq
  have hbM := (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable x σ L b.val).comp hq
  dsimp only [Function.comp_def, q] at haM hbM
  have hm : Measurable (fun ω => reflectedInteriorOccupationCoefficient x σ L a.val (τ ω) ω -
      reflectedInteriorOccupationCoefficient x σ L b.val (τ ω) ω) := haM.sub hbM
  have hM : MemLp (fun ω => reflectedInteriorLevelError L hL x hσ T a b ω / σ ^ 2)
      2 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using
      (reflectedInteriorLevelError_memLp L hL x hσ T a b).mul_const (σ ^ 2)⁻¹
  apply hM.mono' hm.aestronglyMeasurable
  filter_upwards [reflectedInteriorOccupation_level_compact_bound_ae L hL x hσ T a b, hτT] with ω hb ht
  exact hb (τ ω) ht

theorem reflectedInteriorOccupation_random_difference_secondMoment_le (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L)
    (τ : (ℕ → ℝ) → ℝ≥0) (hτ : Measurable τ) (hτT : ∀ᵐ ω ∂brownianDyadicMeasure, τ ω ≤ T) :
    (∫ ω, (reflectedInteriorOccupationCoefficient x σ L a.val (τ ω) ω -
      reflectedInteriorOccupationCoefficient x σ L b.val (τ ω) ω) ^ 2 ∂brownianDyadicMeasure) ≤
      (∫ ω, reflectedInteriorLevelError L hL x hσ T a b ω ^ 2 ∂brownianDyadicMeasure) / (σ ^ 2) ^ 2 := by
  have hM : MemLp (fun ω => reflectedInteriorLevelError L hL x hσ T a b ω / σ ^ 2)
      2 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using
      (reflectedInteriorLevelError_memLp L hL x hσ T a b).mul_const (σ ^ 2)⁻¹
  calc
    _ ≤ ∫ ω, (reflectedInteriorLevelError L hL x hσ T a b ω / σ ^ 2) ^ 2 ∂brownianDyadicMeasure := by
      apply integral_mono_ae
        (reflectedInteriorOccupation_random_difference_memLp L hL x hσ T a b τ hτ hτT).integrable_sq
        hM.integrable_sq
      filter_upwards [reflectedInteriorOccupation_level_compact_bound_ae L hL x hσ T a b, hτT] with ω hb ht
      have hh := hb (τ ω) ht
      have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
      simpa only [sq_abs] using hsq
    _ = _ := by simp only [div_eq_mul_inv, mul_pow, inv_pow, integral_mul_const]

theorem reflectedInteriorOccupation_random_horizons_level_tendsto (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0)
    {u : ℕ → Ioo (0 : ℝ) L} {a : Ioo (0 : ℝ) L} (hu : Tendsto u atTop (𝓝 a))
    (τ : ℕ → (ℕ → ℝ) → ℝ≥0) (hτ : ∀ n, Measurable (τ n))
    (hτT : ∀ n, ∀ᵐ ω ∂brownianDyadicMeasure, τ n ω ≤ T) :
    Tendsto (fun n => ∫ ω, (reflectedInteriorOccupationCoefficient x σ L (u n).val (τ n ω) ω -
      reflectedInteriorOccupationCoefficient x σ L a.val (τ n ω) ω) ^ 2 ∂brownianDyadicMeasure)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _))
    (fun n => reflectedInteriorOccupation_random_difference_secondMoment_le L hL x hσ T
      (u n) a (τ n) (hτ n) (hτT n))
  simpa only [zero_div] using
    (reflectedInteriorLevelError_square_tendsto_zero L hL x hσ T hu).div_const ((σ ^ 2) ^ 2)

end TimeTraps.Probability
