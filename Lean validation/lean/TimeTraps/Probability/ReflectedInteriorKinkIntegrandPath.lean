module

public import TimeTraps.Probability.ReflectedInteriorKinkIntegrand
public import TimeTraps.Probability.BrownianIntegralContinuousGlobalCompact
public import TimeTraps.Probability.BrownianJointMeasurability

@[expose] public section

/-! Continuous finite-horizon versions of the actual original-Brownian
interior-kink integral. Fixed-time identification is almost sure; two
fixed horizons agree at every common time on one full-measure event,
obtained from a countable dense time set and continuity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def reflectedInteriorKinkHorizonPath (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath (reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL a ha x hσ T)

theorem reflectedInteriorKinkHorizonPath_continuous (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => reflectedInteriorKinkHorizonPath L hL a ha x hσ T t ω) :=
  brownianIntegralGlobalPath_continuous _ ω

theorem reflectedInteriorKinkHorizonPath_jointlyMeasurable (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedInteriorKinkHorizonPath L hL a ha x hσ T p.1 p.2) :=
  brownianIntegralGlobalPath_jointlyMeasurable _

theorem reflectedInteriorKinkHorizonPath_integral_ae (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    reflectedInteriorKinkHorizonPath L hL a ha x hσ T t =ᵐ[brownianDyadicMeasure]
      reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL a ha x hσ (min t T) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL a ha x hσ T) t
  rw [reflectedInteriorKinkIntegral_upTo] at he
  exact he

theorem reflectedInteriorKinkHorizonPath_raw_aestronglyMeasurable (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (reflectedInteriorKinkHorizonPath L hL a ha x hσ T t)
      brownianDyadicMeasure :=
  brownianIntegralGlobalPath_raw_aestronglyMeasurable _ t

theorem reflectedInteriorKinkHorizonPath_zero_ae (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    reflectedInteriorKinkHorizonPath L hL a ha x hσ T 0 =ᵐ[brownianDyadicMeasure] (fun _ => 0) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL a ha x hσ T) 0
  rw [brownianIntegralUpTo_zero] at he
  exact he.trans (Lp.coeFn_zero ℝ 2 brownianDyadicMeasure)

theorem reflectedInteriorKinkHorizonPath_compatible (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ S →
      reflectedInteriorKinkHorizonPath L hL a ha x hσ S t ω =
        reflectedInteriorKinkHorizonPath L hL a ha x hσ T t ω := by
  have ht (t : BrownianCompactTime S) :
      reflectedInteriorKinkHorizonPath L hL a ha x hσ S t.val =ᵐ[brownianDyadicMeasure]
        reflectedInteriorKinkHorizonPath L hL a ha x hσ T t.val := by
    have hs := reflectedInteriorKinkHorizonPath_integral_ae L hL a ha x hσ S t.val
    have hh := reflectedInteriorKinkHorizonPath_integral_ae L hL a ha x hσ T t.val
    rw [min_eq_left t.property.2] at hs
    rw [min_eq_left (t.property.2.trans hST)] at hh
    exact hs.trans hh.symm
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      reflectedInteriorKinkHorizonPath L hL a ha x hσ S (denseSeq (BrownianCompactTime S) n).val ω =
        reflectedInteriorKinkHorizonPath L hL a ha x hσ T (denseSeq (BrownianCompactTime S) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime S) n))
  filter_upwards [hall] with ω hω t hts
  have he := (denseRange_denseSeq (BrownianCompactTime S)).equalizer
    ((reflectedInteriorKinkHorizonPath_continuous L hL a ha x hσ S ω).comp continuous_subtype_val)
    ((reflectedInteriorKinkHorizonPath_continuous L hL a ha x hσ T ω).comp continuous_subtype_val)
    (funext hω)
  exact congrFun he ⟨t, zero_le, hts⟩

end TimeTraps.Probability

end
