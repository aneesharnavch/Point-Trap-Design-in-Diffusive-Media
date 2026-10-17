module

public import TimeTraps.Probability.ReflectedLocalTimeBandErrorFamily

@[expose] public section

/-! The maximal-error family has a jointly measurable nonnegative
representative, agreeing at each fixed level with the actual bound.
This enables product integration while retaining the all-time bound. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedBandErrorVersion (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) (ω : ℕ → ℝ) : ℝ :=
  max 0 (l2FamilyMeasurableVersion (reflectedBandErrorL2_continuous L hL x hσ T a).stronglyMeasurable b ω)

theorem reflectedBandErrorVersion_jointlyMeasurable (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedBandErrorVersion L hL x hσ T a p.1 p.2) :=
  measurable_const.max (l2FamilyMeasurableVersion_jointlyMeasurable
    (reflectedBandErrorL2_continuous L hL x hσ T a).stronglyMeasurable)

theorem reflectedBandErrorVersion_nonneg (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) (ω : ℕ → ℝ) :
    0 ≤ reflectedBandErrorVersion L hL x hσ T a b ω := le_max_left _ _

theorem reflectedBandErrorVersion_actual_ae (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) :
    reflectedBandErrorVersion L hL x hσ T a b =ᵐ[brownianDyadicMeasure]
      reflectedInteriorLevelError L hL x hσ T (reflectedBandClippedLevel a b) a := by
  filter_upwards [l2FamilyMeasurableVersion_ae
    (reflectedBandErrorL2_continuous L hL x hσ T a).stronglyMeasurable b,
    reflectedBandErrorL2_coe L hL x hσ T a b] with ω hv he
  change max 0 _ = _
  rw [hv, he, max_eq_right]
  unfold reflectedInteriorLevelError
  positivity

theorem reflectedBandErrorVersion_ae (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) :
    reflectedBandErrorVersion L hL x hσ T a b =ᵐ[brownianDyadicMeasure]
      reflectedBandErrorL2 L hL x hσ T a b :=
  (reflectedBandErrorVersion_actual_ae L hL x hσ T a b).trans
    (reflectedBandErrorL2_coe L hL x hσ T a b).symm

theorem reflectedBandErrorVersion_memLp (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) :
    MemLp (reflectedBandErrorVersion L hL x hσ T a b) 2 brownianDyadicMeasure :=
  (Lp.memLp (reflectedBandErrorL2 L hL x hσ T a b)).ae_eq
    (reflectedBandErrorVersion_ae L hL x hσ T a b).symm

theorem reflectedBandErrorVersion_bound_ae (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |reflectedInteriorCorrection x σ L (reflectedBandClippedLevel a b).val t ω -
        reflectedInteriorCorrection x σ L a.val t ω| ≤ reflectedBandErrorVersion L hL x hσ T a b ω := by
  filter_upwards [reflectedBandErrorVersion_actual_ae L hL x hσ T a b,
    reflectedInteriorLevelError_bound_ae L hL x hσ T (reflectedBandClippedLevel a b) a] with ω hv hb
  rw [hv]
  exact hb

end TimeTraps.Probability
