module

public import TimeTraps.Probability.ContinuousPathLocalTimeCocycle

@[expose] public section

/-! The scalar band limit is nonanticipating on every path, including
outside the good-path set. On good paths it equals the canonical
continuous curve. Thus the realized local time is adapted to every
filtration to which the continuous particle process is adapted. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

def continuousPathLocalTimeValue (a : ℝ) (m : ℝ → ℝ) (t : ℝ≥0)
    (p : ReversibleNeumannFullPath) : ℝ :=
  limUnder atTop (fun n => continuousPathOccupationBand a (occupationBandRadius n)
    (m (occupationBandRadius n)) p t)

theorem HasContinuousOccupationLocalTime.value_eq {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) (t : ℝ≥0) :
    continuousPathLocalTimeValue a m t p = continuousPathLocalTime a m p t :=
  (h.eval_tendsto t).limUnder_eq

theorem continuousPathLocalTimeValue_jointlyMeasurable (a : ℝ) (m : ℝ → ℝ) :
    Measurable (fun q : ℝ≥0 × ReversibleNeumannFullPath => continuousPathLocalTimeValue a m q.1 q.2) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  apply Measurable.stronglyMeasurable
  exact continuous_eval.measurable.comp
    (((continuousPathOccupationBand_measurable a (occupationBandRadius n)
      (m (occupationBandRadius n))).comp measurable_snd).prodMk measurable_fst)

theorem continuousPathLocalTimeValue_measurable (a : ℝ) (m : ℝ → ℝ) (t : ℝ≥0) :
    Measurable (continuousPathLocalTimeValue a m t) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  exact ((continuous_eval_const t).measurable.comp
    (continuousPathOccupationBand_measurable a (occupationBandRadius n)
      (m (occupationBandRadius n)))).stronglyMeasurable

theorem continuousPathOccupationBand_prefix (a h m : ℝ) (p q : ReversibleNeumannFullPath)
    (t : ℝ≥0) (hpq : EqOn p q (Icc 0 t)) :
    continuousPathOccupationBand a h m p t = continuousPathOccupationBand a h m q t := by
  apply congrArg (fun z : ℝ => z / m)
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' := uIcc_of_le t.property ▸ hr
  change brownianBandIndicator a h (p r.toNNReal) = brownianBandIndicator a h (q r.toNNReal)
  rw [hpq ⟨zero_le, Real.toNNReal_le_iff_le_coe.mpr hr'.2⟩]

theorem continuousPathLocalTimeValue_prefix (a : ℝ) (m : ℝ → ℝ)
    (p q : ReversibleNeumannFullPath) (t : ℝ≥0) (hpq : EqOn p q (Icc 0 t)) :
    continuousPathLocalTimeValue a m t p = continuousPathLocalTimeValue a m t q := by
  unfold continuousPathLocalTimeValue
  congr 1
  funext n
  exact continuousPathOccupationBand_prefix a (occupationBandRadius n) (m (occupationBandRadius n)) p q t hpq

def continuousPathStop (t : ℝ≥0) (p : ReversibleNeumannFullPath) : ReversibleNeumannFullPath :=
  ⟨fun s => p (min s t), p.continuous.comp (continuous_id.min continuous_const)⟩

theorem continuousPathLocalTimeValue_stop (a : ℝ) (m : ℝ → ℝ) (t : ℝ≥0)
    (p : ReversibleNeumannFullPath) :
    continuousPathLocalTimeValue a m t (continuousPathStop t p) = continuousPathLocalTimeValue a m t p := by
  apply continuousPathLocalTimeValue_prefix
  intro s hs
  change p (min s t) = p s
  rw [min_eq_left hs.2]

theorem continuousPathLocalTimeValue_stronglyAdapted {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (G : Filtration ℝ≥0 mΩ) (P : Ω → ReversibleNeumannFullPath)
    (hP : ∀ t, StronglyMeasurable[G t] (fun ω => P ω t)) (a : ℝ) (m : ℝ → ℝ) :
    StronglyAdapted G (fun t ω => continuousPathLocalTimeValue a m t (P ω)) := by
  intro t
  have hstop : Measurable[G t] (fun ω => continuousPathStop t (P ω)) := by
    let : MeasurableSpace Ω := G t
    apply reversibleNeumannFullPathSample_measurableEmbedding.measurable_comp_iff.mp
    apply measurable_pi_lambda
    intro n
    exact ((hP (min (denseSeq ℝ≥0 n) t)).mono (G.mono (min_le_right _ _))).measurable
  have hv := (continuousPathLocalTimeValue_measurable a m t).comp hstop
  simpa only [Function.comp_def, continuousPathLocalTimeValue_stop] using hv.stronglyMeasurable

theorem HasContinuousOccupationLocalTime.value_cocycle {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) (s t : ℝ≥0) :
    continuousPathLocalTimeValue a m (s + t) p = continuousPathLocalTimeValue a m s p +
      continuousPathLocalTimeValue a m t (continuousPathShift s p) := by
  rw [h.value_eq, h.value_eq, (h.shift s).value_eq]
  exact h.cocycle s t

end TimeTraps.Probability

end
