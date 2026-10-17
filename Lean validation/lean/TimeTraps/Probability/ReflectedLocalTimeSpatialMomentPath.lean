module

public import TimeTraps.Probability.ReflectedAtomicHazardData
public import TimeTraps.Probability.BrownianIntegralCompactMaximalPath

@[expose] public section

/-! A measurable continuous compact-time representative of each actual
reflected local-time path. Equality with the original field holds on its
fixed-level all-time regular event; no common event over all levels is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedLocalTimeCompactPath (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : ℝ) (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) := by
  classical
  exact if hr : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω then
    ⟨fun t => reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω,
      ((reflectedInteriorCorrection_continuous (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL hr).div_const _).comp
        continuous_subtype_val⟩ else 0

theorem reflectedLocalTimeCompactPath_apply (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : ℝ) {ω : ℕ → ℝ}
    (hr : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω) (t : BrownianCompactTime T) :
    reflectedLocalTimeCompactPath L hL D hD x T a ω t =
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω := by
  simp only [reflectedLocalTimeCompactPath, dif_pos hr]
  rfl

theorem reflectedLocalTimeCompactPath_evaluation_measurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : ℝ) (t : BrownianCompactTime T) :
    Measurable (fun ω => reflectedLocalTimeCompactPath L hL D hD x T a ω t) := by
  classical
  let q : (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) := fun ω => (t.val, ω)
  have hq : Measurable q := measurable_const.prodMk measurable_id
  have hc := (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable x (Real.sqrt (2 * D)) L a).comp hq
  have he : (fun ω => reflectedLocalTimeCompactPath L hL D hD x T a ω t) =
      (fun ω => if reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω then
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω else 0) := by
    funext ω
    by_cases hr : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω
    · simp only [reflectedLocalTimeCompactPath, dif_pos hr, if_pos hr]
      rfl
    · simp only [reflectedLocalTimeCompactPath, dif_neg hr, if_neg hr, ContinuousMap.zero_apply]
  rw [he]
  exact Measurable.ite (reflectedInteriorLocalTimeRegular_measurableSet x (Real.sqrt (2 * D)) L a)
    hc measurable_const

theorem reflectedLocalTimeCompactPath_stronglyMeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : ℝ) :
    StronglyMeasurable (reflectedLocalTimeCompactPath L hL D hD x T a) :=
  compactPath_stronglyMeasurable _ (reflectedLocalTimeCompactPath_evaluation_measurable L hL D hD x T a)

theorem reflectedLocalTimeCompactPath_sub_norm_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : ℝ) :
    (fun ω => ‖reflectedLocalTimeCompactPath L hL D hD x T a ω -
      reflectedLocalTimeCompactPath L hL D hD x T b ω‖) =ᵐ[brownianDyadicMeasure]
      (fun ω => ⨆ t : BrownianCompactTime T,
        |reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L b t.val ω|) := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a,
    reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L b] with ω ha hb
  rw [(reflectedLocalTimeCompactPath L hL D hD x T a ω -
    reflectedLocalTimeCompactPath L hL D hD x T b ω).norm_eq_iSup_norm]
  simp only [ContinuousMap.sub_apply, reflectedLocalTimeCompactPath_apply L hL D hD x T a ha,
    reflectedLocalTimeCompactPath_apply L hL D hD x T b hb, Real.norm_eq_abs]

end TimeTraps.Probability
