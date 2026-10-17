module

public import TimeTraps.Probability.BrownianLocalTimeBandAverage
public import TimeTraps.Analysis.ContinuousBandAverage
public import TimeTraps.Probability.BrownianLocalTimeGlobal

@[expose] public section

/-! Normalized genuine occupation bands converge in actual L2 to the
Tanaka compensation at every fixed level and finite horizon. For the
constructed Brownian process the limit is the L2 class of its global
continuous local-time path. No almost-sure full-bandwidth limit or
spatial sample continuity is claimed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianBandOccupationL2_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun h : ℝ => brownianBandOccupationL2 hB hjoint a h T)
      (𝓝[>] 0) (𝓝 (brownianTanakaCompensation hB hBm hjoint a T)) := by
  apply (continuous_band_average_tendsto
    (brownianTanakaCompensation_level_continuous hB hBm hjoint T) a).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (brownianBandOccupationL2_eq_average hB hBm hjoint a
    (show 0 ≤ h from (show 0 < h from hh).le) T).symm

theorem brownianBandOccupationL2_seq_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0)
    {h : ℕ → ℝ} (hpos : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => brownianBandOccupationL2 hB hjoint a (h n) T)
      atTop (𝓝 (brownianTanakaCompensation hB hBm hjoint a T)) :=
  (brownianBandOccupationL2_tendsto hB hBm hjoint a T).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hpos⟩)

theorem brownianDyadicBandOccupationL2_globalPath_tendsto (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun h : ℝ => brownianBandOccupationL2 brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_jointly_measurable a h T) (𝓝[>] 0)
      (𝓝 ((brownianLocalTimeGlobalPath_memLp a T).toLp (brownianLocalTimeGlobalPath a T))) := by
  have he : (brownianLocalTimeGlobalPath_memLp a T).toLp (brownianLocalTimeGlobalPath a T) =
      brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable a T := by
    apply Lp.ext
    exact (brownianLocalTimeGlobalPath_memLp a T).coeFn_toLp.trans
      (brownianLocalTimeGlobalPath_compensation_ae a T)
  rw [he]
  exact brownianBandOccupationL2_tendsto brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a T

end TimeTraps.Probability
