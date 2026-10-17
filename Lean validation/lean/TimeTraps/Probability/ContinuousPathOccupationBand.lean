module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemFullPath
public import TimeTraps.Probability.ReflectedLocalTimeBandData

@[expose] public section

/-! Literal occupation bands on the Borel space of continuous paths.
Their time-shift identity is an interval-integral identity and does not
assume any local-time or additive-functional property. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal Topology

def continuousPathShift (s : ℝ≥0) (p : ReversibleNeumannFullPath) : ReversibleNeumannFullPath :=
  ⟨fun t => p (s + t), p.continuous.comp (continuous_const.add continuous_id)⟩

theorem continuousPathShift_continuous (s : ℝ≥0) : Continuous (continuousPathShift s) := by
  exact (ContinuousMap.uniformContinuous_comp_left
    (⟨fun t : ℝ≥0 => s + t, continuous_const.add continuous_id⟩ : C(ℝ≥0, ℝ≥0))).continuous

theorem continuousPathShift_add (s t : ℝ≥0) (p : ReversibleNeumannFullPath) :
    continuousPathShift t (continuousPathShift s p) = continuousPathShift (s + t) p := by
  ext r
  exact congrArg p (add_assoc s t r).symm

theorem continuousPathBand_intervalIntegrable (p : ReversibleNeumannFullPath) (a h u v : ℝ) :
    IntervalIntegrable (fun r : ℝ => brownianBandIndicator a h (p r.toNNReal)) volume u v := by
  have hm : Measurable (fun r : ℝ => brownianBandIndicator a h (p r.toNNReal)) :=
    (brownianBandIndicator_measurable a h).comp
      (p.continuous.comp continuous_real_toNNReal).measurable
  have hi : IntegrableOn (fun r : ℝ => brownianBandIndicator a h (p r.toNNReal)) (uIcc u v) volume :=
    (integrableOn_const (C := (1 : ℝ)) (μ := volume) (s := uIcc u v)
    isCompact_uIcc.measure_ne_top).mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun r => brownianBandIndicator_abs_le_one a h (p r.toNNReal)))
  exact hi.intervalIntegrable

def continuousPathOccupationBand (a h m : ℝ) (p : ReversibleNeumannFullPath) : ReversibleNeumannFullPath :=
  ⟨fun t => (∫ r in (0 : ℝ)..t.val, brownianBandIndicator a h (p r.toNNReal)) / m,
    (((intervalIntegral.continuous_primitive (continuousPathBand_intervalIntegrable p a h) 0).comp
      NNReal.continuous_coe).div_const m)⟩

theorem continuousPathOccupationBand_zero (a h m : ℝ) (p : ReversibleNeumannFullPath) :
    continuousPathOccupationBand a h m p 0 = 0 := by
  simp [continuousPathOccupationBand]

theorem continuousPathOccupationBand_measurable (a h m : ℝ) :
    Measurable (continuousPathOccupationBand a h m) := by
  apply reversibleNeumannFullPathSample_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro n
  have hjoint : Measurable (fun q : ℝ≥0 × ReversibleNeumannFullPath => q.2 q.1) :=
    (continuous_eval.comp (continuous_snd.prodMk continuous_fst)).measurable
  exact (brownianItoDrift_bounded_measurable (B := fun t (p : ReversibleNeumannFullPath) => p t)
    (brownianBandIndicator_measurable a h)
    hjoint
    (denseSeq ℝ≥0 n)).div_const m

theorem continuousPathOccupationBand_monotone (a h m : ℝ) (hm : 0 ≤ m)
    (p : ReversibleNeumannFullPath) : Monotone (continuousPathOccupationBand a h m p) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ hm
  apply intervalIntegral.integral_mono_interval le_rfl s.property hst
    (Eventually.of_forall (fun r => ?_))
    (continuousPathBand_intervalIntegrable p a h 0 t.val)
  rw [brownianBandIndicator_apply]
  split_ifs <;> norm_num

theorem continuousPathOccupationBand_shift (a h m : ℝ) (p : ReversibleNeumannFullPath)
    (s : ℝ≥0) :
    continuousPathOccupationBand a h m (continuousPathShift s p) =
      continuousPathShift s (continuousPathOccupationBand a h m p) -
        ContinuousMap.const ℝ≥0 (continuousPathOccupationBand a h m p s) := by
  ext t
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuousPathBand_intervalIntegrable p a h 0 s.val)
    (continuousPathBand_intervalIntegrable p a h s.val (s.val + t.val))
  have hs : (∫ r in (0 : ℝ)..t.val, brownianBandIndicator a h (p (s + r.toNNReal))) =
      ∫ r in s.val..s.val + t.val, brownianBandIndicator a h (p r.toNNReal) := by
    calc
      _ = ∫ r in (0 : ℝ)..t.val, brownianBandIndicator a h (p ((s : ℝ) + r).toNNReal) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr0 : 0 ≤ r := (uIcc_of_le t.property ▸ hr).1
        apply congrArg (fun z => brownianBandIndicator a h (p z))
        apply NNReal.coe_injective
        change (s : ℝ) + (r.toNNReal : ℝ) = (((s : ℝ) + r).toNNReal : ℝ)
        exact (congrArg (fun z : ℝ => (s : ℝ) + z) (Real.coe_toNNReal r hr0)).trans
          (Real.coe_toNNReal ((s : ℝ) + r) (add_nonneg s.property hr0)).symm
      _ = _ := by
        convert! intervalIntegral.integral_comp_add_left
          (fun r : ℝ => brownianBandIndicator a h (p r.toNNReal))
          (a := 0) (b := t.val) s.val using 1
        simp only [add_zero]
  change (∫ r in (0 : ℝ)..t.val, brownianBandIndicator a h (p (s + r.toNNReal))) / m =
    (∫ r in (0 : ℝ)..(s.val + t.val), brownianBandIndicator a h (p r.toNNReal)) / m -
      (∫ r in (0 : ℝ)..s.val, brownianBandIndicator a h (p r.toNNReal)) / m
  rw [hs, ← sub_div]
  exact congrArg (fun z : ℝ => z / m) (eq_sub_iff_add_eq.mpr (by linarith [hi]))

end TimeTraps.Probability

end
