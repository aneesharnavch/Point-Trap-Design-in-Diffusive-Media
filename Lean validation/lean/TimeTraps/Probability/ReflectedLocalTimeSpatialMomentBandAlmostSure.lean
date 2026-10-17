module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentOccupation
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentAverage

@[expose] public section

/-! The original ordinary occupation bands converge almost surely for
the full positive-radius filter, uniformly over the entire compact time
horizon. The target is the original fixed-level coefficient; all radius
and time comparisons take place on a single event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedOccupationBand_window_uniform_as (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r)
    (hr : r < L) (a : Ioo (0 : ℝ) L) (ha : a.val ∈ Ioo l r) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime T,
        |reflectedOccupationBand L D x a.val h t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|)
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [reflectedLocalTimeWindow_occupation_all_tests_times_ae L hL D hD x T l r hl hlr hr,
    reflectedLocalTimeSpatialVersion_fixed_level_all_times L hL D hD x T
      (reflectedSpatialWindowPoint L l r hl hlr hr a.val)] with ω hocc hcenter
  have hc (t : BrownianCompactTime T) :
      reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr a.val ω t =
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω := by
    have he := hcenter t
    rw [reflectedSpatialWindowPoint_of_mem L l r hl hlr hr ⟨ha.1.le, ha.2.le⟩] at he
    exact he
  have hlim : Tendsto (fun h : ℝ => ‖reflectedLocalTimeWindowAverage L hL D hD x T l r hl hlr hr a.val h ω -
      reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr a.val ω‖) (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((reflectedLocalTimeWindowAverage_tendsto L hL D hD x T l r hl hlr hr a.val ω).sub_const
        (reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr a.val ω)).norm
  apply hlim.congr'
  have hm : 0 < min (a.val - l) (r - a.val) := lt_min (sub_pos.mpr ha.1) (sub_pos.mpr ha.2)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hm).filter_mono nhdsWithin_le_nhds] with h hh hsmall
  have hh' : 0 < h := hh
  have hsub : Ioo (a.val - h) (a.val + h) ⊆ Icc l r := by
    intro z hz
    exact ⟨by linarith [(lt_min_iff.mp hsmall).1, hz.1],
      by linarith [(lt_min_iff.mp hsmall).2, hz.2]⟩
  have hsupp : ∀ z ∉ Icc l r, brownianBandIndicator a.val h z = 0 := by
    intro z hz
    have hn : z ∉ Ioo (a.val - h) (a.val + h) := fun h => hz (hsub h)
    exact indicator_of_notMem hn (fun _ => (1 : ℝ))
  have hband (t : BrownianCompactTime T) : reflectedOccupationBand L D x a.val h t.val ω =
      reflectedLocalTimeWindowAverage L hL D hD x T l r hl hlr hr a.val h ω t := by
    have he := hocc (brownianBandIndicator a.val h) (brownianBandIndicator_measurable a.val h) 1
      (brownianBandIndicator_abs_le_one a.val h) hsupp t
    have hp := reflectedLocalTimeWindowTestPath_band L hL D hD x T l r hl hlr hr a.val hh' hsub ω
    change (1 / (2 * h)) * brownianItoDrift (foldedTrajectory L D x brownianDyadicPath)
      (brownianBandIndicator a.val h) t.val ω = _
    rw [he, hp]
    rfl
  rw [(reflectedLocalTimeWindowAverage L hL D hD x T l r hl hlr hr a.val h ω -
    reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr a.val ω).norm_eq_iSup_norm]
  congr 1
  funext t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, ← hband t, hc t]

theorem reflectedOccupationBand_compact_uniform_as (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime T,
        |reflectedOccupationBand L D x a.val h t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|)
        (𝓝[>] 0) (𝓝 0) :=
  reflectedOccupationBand_window_uniform_as L hL D hD x T (a.val / 2) ((L + a.val) / 2)
    (by linarith [a.property.1]) (by linarith) (by linarith [a.property.2]) a
    ⟨by linarith [a.property.1], by linarith [a.property.2]⟩

end TimeTraps.Probability
