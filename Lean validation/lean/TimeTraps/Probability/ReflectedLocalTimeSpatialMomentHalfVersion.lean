module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentParameters
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentKolmogorovVersion

@[expose] public section

/-! The complete-space continuity construction applies to the actual
compact-time local-time process on each of two spatial parameterizations.
Every hypothesis is discharged by the proved spatial fourth moment. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedLocalTimeParameterProcess (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) (t : ℝ≥0) (ω : ℕ → ℝ) :
    C(BrownianCompactTime T, ℝ) :=
  reflectedLocalTimeCompactPath L hL D hD x T (reflectedSpatialParameter L hL right t).val ω

theorem reflectedLocalTimeParameterProcess_stronglyMeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) (t : ℝ≥0) :
    StronglyMeasurable (reflectedLocalTimeParameterProcess L hL D hD x T right t) :=
  reflectedLocalTimeCompactPath_stronglyMeasurable L hL D hD x T _

theorem reflectedLocalTimeParameterProcess_integrable_fourth (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) (s t : ℝ≥0) :
    Integrable (fun ω => dist (reflectedLocalTimeParameterProcess L hL D hD x T right s ω)
      (reflectedLocalTimeParameterProcess L hL D hD x T right t ω) ^ 4) brownianDyadicMeasure := by
  simpa only [dist_eq_norm, reflectedLocalTimeParameterProcess] using brownian_memLp_four_integrable_fourth
    (reflectedLocalTimeCompactPath_sub_memLp_four L hL D hD x T
      (reflectedSpatialParameter L hL right s) (reflectedSpatialParameter L hL right t)).norm

theorem reflectedLocalTimeParameterProcess_fourth_moment (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) (s t : ℝ≥0) :
    (∫ ω, dist (reflectedLocalTimeParameterProcess L hL D hD x T right s ω)
      (reflectedLocalTimeParameterProcess L hL D hD x T right t ω) ^ 4 ∂brownianDyadicMeasure) ≤
      (reflectedSpatialFourthConstant L D T * L ^ 2) * dist s t ^ 2 := by
  have he := reflectedLocalTimeCompactPath_spatial_fourth_moment L hL D hD x T
    (reflectedSpatialParameter L hL right s) (reflectedSpatialParameter L hL right t)
  have hb := pow_le_pow_left₀ (abs_nonneg _) (reflectedSpatialParameter_lipschitz_bound L hL right s t) 2
  have hm := mul_le_mul_of_nonneg_left hb (reflectedSpatialFourthConstant_nonneg L hD T)
  change (∫ ω, dist (reflectedLocalTimeParameterProcess L hL D hD x T right s ω)
    (reflectedLocalTimeParameterProcess L hL D hD x T right t ω) ^ 4 ∂brownianDyadicMeasure) ≤ _
  simp only [dist_eq_norm]
  refine he.trans (hm.trans_eq ?_)
  ring

noncomputable def reflectedLocalTimeHalfVersion (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) : ℝ≥0 → (ℕ → ℝ) → C(BrownianCompactTime T, ℝ) :=
  fourthContinuousVersion (reflectedLocalTimeParameterProcess L hL D hD x T right)

theorem reflectedLocalTimeHalfVersion_continuous (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) (ω : ℕ → ℝ) :
    Continuous (fun t => reflectedLocalTimeHalfVersion L hL D hD x T right t ω) :=
  fourthContinuousVersion_continuous _ ω

theorem reflectedLocalTimeHalfVersion_stronglyMeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) (t : ℝ≥0) :
    StronglyMeasurable (reflectedLocalTimeHalfVersion L hL D hD x T right t) :=
  fourthContinuousVersion_stronglyMeasurable
    (reflectedLocalTimeParameterProcess_stronglyMeasurable L hL D hD x T right) t

theorem reflectedLocalTimeHalfVersion_ae_eq (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (right : Bool) (t : ℝ≥0) :
    reflectedLocalTimeHalfVersion L hL D hD x T right t =ᵐ[brownianDyadicMeasure]
      reflectedLocalTimeParameterProcess L hL D hD x T right t :=
  fourthContinuousVersion_ae_eq
    (reflectedLocalTimeParameterProcess_integrable_fourth L hL D hD x T right)
    (reflectedLocalTimeParameterProcess_fourth_moment L hL D hD x T right) t

theorem reflectedLocalTimeHalfVersion_midpoint_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, reflectedLocalTimeHalfVersion L hL D hD x T false 0 ω =
      reflectedLocalTimeHalfVersion L hL D hD x T true 0 ω := by
  filter_upwards [reflectedLocalTimeHalfVersion_ae_eq L hL D hD x T false 0,
    reflectedLocalTimeHalfVersion_ae_eq L hL D hD x T true 0] with ω hleft hright
  rw [hleft, hright]
  unfold reflectedLocalTimeParameterProcess
  rw [reflectedSpatialParameter_zero, reflectedSpatialParameter_zero]

end TimeTraps.Probability
