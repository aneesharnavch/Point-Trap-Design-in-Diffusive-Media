module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentTestData
public import TimeTraps.Analysis.ContinuousBandAverage

@[expose] public section

/-! The actual normalization1/(2h) is the continuous-path-valued spatial
average. Continuity yields convergence for the full positive-radius filter,
not merely for a chosen sequence. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedLocalTimeWindowAverage (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L)
    (a h : ℝ) (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) :=
  (1 / (2 * h)) • ∫ z in (a - h)..(a + h),
    reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω

theorem reflectedLocalTimeWindowTestPath_band (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (hsub : Ioo (a - h) (a + h) ⊆ Icc l r) (ω : ℕ → ℝ) :
    reflectedLocalTimeWindowTestPath L hL D hD x T l r hl hlr hr (brownianBandIndicator a h) ω =
      ∫ z in (a - h)..(a + h), reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω := by
  let V := fun z => reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω
  have he : (fun z => brownianBandIndicator a h z • V z) = (Ioo (a - h) (a + h)).indicator V := by
    funext z
    by_cases hz : z ∈ Ioo (a - h) (a + h)
    · simp only [brownianBandIndicator, indicator_of_mem hz, one_smul]
    · simp only [brownianBandIndicator, indicator_of_notMem hz, zero_smul]
  change (∫ z in Icc l r, brownianBandIndicator a h z • V z) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    have hn : z ∉ Ioo (a - h) (a + h) := fun h => hz (hsub h)
    simp only [brownianBandIndicator, indicator_of_notMem hn, zero_smul]), he,
    integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : a - h ≤ a + h)]

theorem reflectedLocalTimeWindowAverage_tendsto (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L)
    (a : ℝ) (ω : ℕ → ℝ) :
    Tendsto (fun h : ℝ => reflectedLocalTimeWindowAverage L hL D hD x T l r hl hlr hr a h ω)
      (𝓝[>] 0) (𝓝 (reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr a ω)) :=
  continuous_band_average_tendsto (reflectedLocalTimeWindowVersion_continuous L hL D hD x T l r hl hlr hr ω) a

end TimeTraps.Probability
