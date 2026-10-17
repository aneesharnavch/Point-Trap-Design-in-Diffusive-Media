module

public import TimeTraps.Probability.ReflectedLocalTimeBandData
public import TimeTraps.Probability.ReflectedAtomicHazardData
public import TimeTraps.Probability.BrownianIntegralCompactMaximalPath

@[expose] public section

/-! A measurable continuous-path representative of the genuine band
error on a compact horizon. Its norm is the literal supremum error on
the existing fixed-level regular event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedBandErrorCompactPath (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a h : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) := by
  classical
  exact if hr : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω then
    ⟨fun t => reflectedOccupationBand L D x a h t.val ω -
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω,
      ((reflectedOccupationBand_continuous L D x a h ω).sub
        ((reflectedInteriorCorrection_continuous (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL hr).div_const _)).comp
          continuous_subtype_val⟩ else 0

theorem reflectedBandErrorCompactPath_apply (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a h : ℝ) (T : ℝ≥0) {ω : ℕ → ℝ}
    (hr : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω) (t : BrownianCompactTime T) :
    reflectedBandErrorCompactPath L hL D hD x a h T ω t =
      reflectedOccupationBand L D x a h t.val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω := by
  simp only [reflectedBandErrorCompactPath, dif_pos hr]
  rfl

theorem reflectedBandErrorCompactPath_evaluation_measurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a h : ℝ) (T : ℝ≥0) (t : BrownianCompactTime T) :
    Measurable (fun ω => reflectedBandErrorCompactPath L hL D hD x a h T ω t) := by
  classical
  let q : (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) := fun ω => (t.val, ω)
  have hq : Measurable q := measurable_const.prodMk measurable_id
  have hb := (reflectedOccupationBand_jointlyMeasurable L D x a h).comp hq
  have hc := (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable x (Real.sqrt (2 * D)) L a).comp hq
  have he : (fun ω => reflectedBandErrorCompactPath L hL D hD x a h T ω t) =
      (fun ω => if reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω then
        reflectedOccupationBand L D x a h t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω else 0) := by
    funext ω
    by_cases hr : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω
    · simp only [reflectedBandErrorCompactPath, dif_pos hr, if_pos hr]
      rfl
    · simp only [reflectedBandErrorCompactPath, dif_neg hr, if_neg hr, ContinuousMap.zero_apply]
  rw [he]
  exact Measurable.ite (reflectedInteriorLocalTimeRegular_measurableSet x (Real.sqrt (2 * D)) L a)
    (hb.sub hc) measurable_const

theorem reflectedBandErrorCompactPath_stronglyMeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a h : ℝ) (T : ℝ≥0) :
    StronglyMeasurable (reflectedBandErrorCompactPath L hL D hD x a h T) :=
  compactPath_stronglyMeasurable _ (reflectedBandErrorCompactPath_evaluation_measurable L hL D hD x a h T)

theorem reflectedBandErrorCompactPath_norm_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a h : ℝ) (T : ℝ≥0) :
    (fun ω => ‖reflectedBandErrorCompactPath L hL D hD x a h T ω‖) =ᵐ[brownianDyadicMeasure]
      (fun ω => ⨆ t : BrownianCompactTime T,
        |reflectedOccupationBand L D x a h t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω|) := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a] with ω hr
  rw [(reflectedBandErrorCompactPath L hL D hD x a h T ω).norm_eq_iSup_norm]
  simp only [reflectedBandErrorCompactPath_apply L hL D hD x a h T hr, Real.norm_eq_abs]

end TimeTraps.Probability
