module

public import TimeTraps.Analysis.GraphPhysicalClockRealIso
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! The actual Borel-speed Stieltjes measure is sent to ordinary time
by the clock. Restricting to positive times gives the exact change of
variables without any differentiability of the speed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped NNReal ENNReal

theorem GraphPhysicalClockSpeed.realOrderIso_measurePreserving (v : GraphPhysicalClockSpeed) :
    MeasurePreserving v.realOrderIso v.stieltjes.measure volume := by
  refine ⟨v.realOrderIso.continuous.measurable, ?_⟩
  symm
  apply Measure.ext_of_Ioc
  intro a b _
  rw [Measure.map_apply v.realOrderIso.continuous.measurable measurableSet_Ioc,
    v.realOrderIso.preimage_Ioc, StieltjesFunction.measure_Ioc, Real.volume_Ioc]
  change ENNReal.ofReal (b - a) = ENNReal.ofReal
    (v.realOrderIso (v.realOrderIso.symm b) - v.realOrderIso (v.realOrderIso.symm a))
  rw [v.realOrderIso.apply_symm_apply, v.realOrderIso.apply_symm_apply]

theorem GraphPhysicalClockSpeed.realOrderIso_positive_measurePreserving (v : GraphPhysicalClockSpeed) :
    MeasurePreserving v.realOrderIso (v.stieltjes.measure.restrict (Ioi (0 : ℝ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hp : v.realOrderIso ⁻¹' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext s
    change 0 < v.realOrderIso s ↔ 0 < s
    simpa only [v.realOrderIso_zero] using
      (show v.realOrderIso 0 < v.realOrderIso s ↔ 0 < s from v.realOrderIso.lt_iff_lt)
  simpa only [hp] using v.realOrderIso_measurePreserving.restrict_preimage (s := Ioi (0 : ℝ)) measurableSet_Ioi

theorem GraphPhysicalClockSpeed.positive_integral_substitution (v : GraphPhysicalClockSpeed)
    (w : ℝ≥0 → ℝ) :
    (∫ t in Ioi (0 : ℝ), w t.toNNReal) =
      ∫ s in Ioi (0 : ℝ), w (v.clock s.toNNReal) * v.rate s.toNNReal := by
  have he := v.realOrderIso_positive_measurePreserving.integral_comp
    v.realOrderIso.toHomeomorph.measurableEmbedding (fun t : ℝ => w t.toNNReal)
  rw [← he, v.stieltjes_measure, restrict_withDensity measurableSet_Ioi]
  have hd : Measurable (fun r : ℝ => ENNReal.ofReal (v.rate r.toNNReal)) :=
    (v.measurable_rate.comp continuous_real_toNNReal.measurable).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict (Ioi (0 : ℝ)))
    (g := fun r => w (v.realOrderIso r).toNNReal) hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hc : v.realOrderIso s = (v.clock s.toNNReal : ℝ) := by
    have hh := v.realOrderIso_clock s.toNNReal
    simpa only [Real.coe_toNNReal s hs.le] using hh
  rw [hc, Real.toNNReal_coe, ENNReal.toReal_ofReal (v.rate_pos _).le]
  exact mul_comm _ _

end TimeTraps.Analysis
