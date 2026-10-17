module

public import TimeTraps.Analysis.GraphPhysicalClockStieltjes
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Integrating against the physical-clock Stieltjes measure is exactly
integration against its original Borel rate. Continuous time weights
have genuine absolute integrability on both sides. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped NNReal ENNReal

theorem GraphPhysicalClockSpeed.stieltjes_weighted_integral (v : GraphPhysicalClockSpeed)
    (w : ℝ≥0 → ℝ) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal ∂v.stieltjes.measure) =
      ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal * v.rate r.toNNReal := by
  rw [v.stieltjes_measure, restrict_withDensity measurableSet_Ioc]
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := volume.restrict (Ioc (0 : ℝ) T.val))
    (g := fun r : ℝ => w r.toNNReal)
    (show Measurable (fun r : ℝ => ENNReal.ofReal (v.rate r.toNNReal)) from
      (v.measurable_rate.comp continuous_real_toNNReal.measurable).ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
  refine he.trans ?_
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  change (ENNReal.ofReal (v.rate r.toNNReal)).toReal * w r.toNNReal = _
  rw [ENNReal.toReal_ofReal (v.rate_pos r.toNNReal).le, mul_comm]

theorem GraphPhysicalClockSpeed.stieltjes_weighted_integrable (v : GraphPhysicalClockSpeed)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (T : ℝ≥0) :
    IntegrableOn (fun r => w r.toNNReal) (Ioc (0 : ℝ) T.val) v.stieltjes.measure ∧
      IntegrableOn (fun r => w r.toNNReal * v.rate r.toNNReal) (Ioc (0 : ℝ) T.val) volume := by
  constructor
  · exact (hw.comp continuous_real_toNNReal).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact ((v.rate_intervalIntegrable 0 T.val).continuousOn_mul
      (hw.comp continuous_real_toNNReal).continuousOn).1

end TimeTraps.Analysis
