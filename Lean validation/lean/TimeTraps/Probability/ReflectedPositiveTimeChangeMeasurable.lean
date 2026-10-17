module

public import TimeTraps.Probability.ReflectedPositiveTimeChangePaths
public import TimeTraps.Probability.ReflectedC2ItoDriftMeasurable
public import TimeTraps.Probability.BrownianItoDriftContinuousAdapted

@[expose] public section

/-! Measurability of the literal positive reflected clock. Compact spatial
continuity gives a bounded continuous folded input, including when the
coefficient has no chosen measurable extension outside the interval.
Adaptation is stated in its proved raw AE strong-measurability form. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def reflectedPositiveTimeInput (L D x : ℝ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  c (reflectedFold L (x + Real.sqrt (2 * D) * z))

theorem reflectedPositiveTimeInput_continuous (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) :
    Continuous (reflectedPositiveTimeInput L D x c) :=
  hc.comp_continuous ((reflectedFold_continuous L).comp
    (continuous_const.add (continuous_const.mul continuous_id)))
    (fun z => reflectedFold_mem L hL (x + Real.sqrt (2 * D) * z))

theorem reflectedPositiveTimeInput_bounded (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) :
    ∃ M : ℝ, ∀ z, |reflectedPositiveTimeInput L D x c z| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨M, fun z => by
    simpa only [reflectedPositiveTimeInput, Real.norm_eq_abs] using
      hM _ (reflectedFold_mem L hL (x + Real.sqrt (2 * D) * z))⟩

theorem reflectedPositiveTimeClock_jointlyMeasurable
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) :
    Measurable (fun p : ℝ≥0 × Ω => reflectedPositiveTimeClock L D x B c p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hx := hjoint.comp hm
  have hH := (reflectedPositiveTimeInput_continuous L hL D x c hc).measurable.comp hx
  have hi := timeIntegral_jointlyMeasurable hH
  have hout := continuous_real_toNNReal.measurable.comp hi
  exact hout

theorem reflectedPositiveTimeClock_measurable
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (s : ℝ≥0) :
    Measurable (reflectedPositiveTimeClock L D x B c s) :=
  (reflectedPositiveTimeClock_jointlyMeasurable hjoint L hL D x c hc).of_uncurry_left

theorem reflectedPositiveTimeClock_raw_aestronglyMeasurable
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (s : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm s]
      (reflectedPositiveTimeClock L D x B c s) P := by
  obtain ⟨M, hM⟩ := reflectedPositiveTimeInput_bounded L hL D x c hc
  have h := brownianItoDrift_continuous_aestronglyMeasurable_past hB hBm
    (reflectedPositiveTimeInput_continuous L hL D x c hc) hM s
  exact continuous_real_toNNReal.comp_aestronglyMeasurable h

end TimeTraps.Probability
