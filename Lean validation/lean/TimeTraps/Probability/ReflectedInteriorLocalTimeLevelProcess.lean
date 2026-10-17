module

public import TimeTraps.Probability.ReflectedInteriorKinkIntegrand
public import TimeTraps.Probability.BrownianLocalTimeLevelProcess
public import TimeTraps.Probability.BrownianPredictableDensityL2Limit

@[expose] public section

/-! The actual reflected kink coefficient varies continuously in L2
with its interior level. Positive-time Gaussian atomlessness removes
the sign discontinuity; no spatial sample continuity is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def reflectedInteriorKinkProcess (B : ℝ≥0 → Ω → ℝ) (L a x σ : ℝ) (T : ℝ≥0) : ℝ × Ω → ℝ :=
  brownianSquareProcess (fun t ω => σ * reflectedInteriorKinkCoefficient L a x σ (B t ω)) T

theorem reflectedInteriorKinkProcess_bound (L : ℝ) (hL : 0 < L) (a x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (p : ℝ × Ω) :
    |reflectedInteriorKinkProcess B L a x σ T p| ≤
      σ * brownianIntervalIndicator 0 T p.1 := by
  apply brownianAdaptedContinuous_cutoff_bound (M := ⟨σ, hσ.le⟩)
  intro t ω
  rw [abs_mul, abs_of_pos hσ]
  exact (mul_le_mul_of_nonneg_left
    (reflectedInteriorKinkCoefficient_bound L hL a x σ (B t ω)) hσ.le).trans_eq (mul_one σ)

theorem reflectedInteriorKinkProcess_memLp [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    MemLp (reflectedInteriorKinkProcess B L a x σ T) 2 (volume.prod P) := by
  apply brownianAdaptedContinuous_cutoff_memLp (M := ⟨σ, hσ.le⟩)
    (measurable_const.mul ((reflectedInteriorKinkCoefficient_measurable L hL a x σ).comp hjoint))
  intro t ω
  rw [abs_mul, abs_of_pos hσ]
  exact (mul_le_mul_of_nonneg_left
    (reflectedInteriorKinkCoefficient_bound L hL a x σ (B t ω)) hσ.le).trans_eq (mul_one σ)

theorem reflectedFold_ne_level_of_notMem_exceptional (L : ℝ) (hL : 0 < L)
    (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (b : ℝ)
    (hb : b ∉ reflectedInteriorKinkExceptional L a x σ) :
    reflectedFold L (x + σ * b) ≠ a := by
  intro he
  obtain ⟨k, hk | hk⟩ := (reflectedFold_eq_iff_lattice L hL (x + σ * b) a
    ⟨ha.1.le, ha.2.le⟩).mp he
  · apply hb
    refine Or.inr (Or.inl ⟨k, ?_⟩)
    exact ((eq_div_iff hσ.ne').mpr (by linarith)).symm
  · apply hb
    refine Or.inr (Or.inr ⟨k, ?_⟩)
    exact ((eq_div_iff hσ.ne').mpr (by linarith)).symm

theorem reflectedInteriorKinkProcess_level_tendsto_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) {u : ℕ → ℝ} {a : ℝ} (ha : a ∈ Ioo 0 L)
    (hu : Tendsto u atTop (𝓝 a)) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂volume.prod P, Tendsto (fun n => reflectedInteriorKinkProcess B L (u n) x σ T p)
      atTop (𝓝 (reflectedInteriorKinkProcess B L a x σ T p)) := by
  filter_upwards [brownian_positive_time_notMem_countable_prod_ae hB hjoint
    (reflectedInteriorKinkExceptional_countable L a x σ) T] with p hp
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hn := reflectedFold_ne_level_of_notMem_exceptional L hL a ha x hσ _ (hp ht)
    exact ((brownianSign_level_tendsto hu hn).mul_const
      (reflectedFoldSlope L (x + σ * B p.1.toNNReal p.2))).const_mul σ |>.const_mul
      ((Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1)
  · have hz (b : ℝ) : reflectedInteriorKinkProcess B L b x σ T p = 0 := by
      change (Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 * _ = 0
      rw [indicator_of_notMem ht, zero_mul]
    simp only [hz]
    exact tendsto_const_nhds

end TimeTraps.Probability
