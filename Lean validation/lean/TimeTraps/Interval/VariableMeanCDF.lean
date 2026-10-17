module

public import TimeTraps.Interval.VariableMeanEnergy

@[expose] public section

/-!
The weighted score is the integral of the actual step CDF. Its finitely many
jumps are handled gap by gap, so no continuity of the CDF is assumed.
-/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ} {K : ℝ} {a : ℝ → ℝ}
  {ha : ContinuousOn a (Icc (0 : ℝ) 1)} {hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x}

theorem IntervalDesign.variable_absorptionCDF
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) (z : ℝ) :
    E.geometry.absorptionCDF E.partition.width z =
      ∑ i, if E.geometry.site i ≤ z then E.partition.width i else 0 := by
  unfold OrderedMedium.absorptionCDF OrderedMedium.sourceSite
  rw [E.variable_source]
  simp only [variableUnitMedium_coordinate]

theorem IntervalDesign.variable_weightedCDF_integral
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) (W : CellWeight) :
    (∫ z in (0 : ℝ)..1, W.value z * (E.geometry.absorptionCDF E.partition.width z - z) ^ 2) =
      weightedCDFScore W E.partition.width E.geometry.site := by
  let f : ℝ → ℝ := fun z => W.value z * (E.geometry.absorptionCDF E.partition.width z - z) ^ 2
  have hgap (e : Fin (n + 1)) {t : ℝ} (ht : t ∈ Ioo 0 (E.geometry.gapLength e)) :
      f (E.geometry.node e.castSucc + t) =
        W.value (E.geometry.node e.castSucc + t) *
          (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t)) ^ 2 := by
    have hc := E.geometry.absorptionCDF_gap E.partition.width e ht
    rw [E.variable_source, variableUnitMedium_coordinate] at hc
    dsimp only [f]
    rw [hc]
  have hnode (v : Fin (n + 2)) : E.geometry.node v ∈ Icc (0 : ℝ) 1 := by
    rw [← E.variable_cdfNode]
    exact cdfNode_mem E.geometry.site E.variable_site_mem v
  have hi : IntervalIntegrable f volume E.geometry.source.left E.geometry.source.right := by
    apply E.geometry.integrable_of_gaps
    intro e
    have hp := (weightedCDF_integrable W (absorptionPrefix E.partition.width e)
      (hnode e.castSucc) (hnode e.succ)).comp_add_left (E.geometry.node e.castSucc)
    simp only [sub_self] at hp
    change IntervalIntegrable (fun t => W.value (E.geometry.node e.castSucc + t) *
      (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t)) ^ 2)
        volume 0 (E.geometry.gapLength e) at hp
    apply hp.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) (E.geometry.gapLength e) := by
      simpa only [uIoo_of_le (E.geometry.gapLength_pos e).le] using ht
    exact (hgap e ht').symm
  have hlocal (e : Fin (n + 1)) :
      (∫ t in (0 : ℝ)..E.geometry.gapLength e, f (E.geometry.node e.castSucc + t)) =
      ∫ z in cdfNode E.geometry.site e.castSucc..cdfNode E.geometry.site e.succ,
        W.value z * (absorptionPrefix E.partition.width e - z) ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..E.geometry.gapLength e,
          W.value (E.geometry.node e.castSucc + t) *
            (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t)) ^ 2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (E.geometry.gapLength_pos e).le
        intro t ht
        exact hgap e ht
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_left
          (fun z => W.value z * (absorptionPrefix E.partition.width e - z) ^ 2)
          (E.geometry.node e.castSucc), add_zero,
          E.variable_cdfNode e.castSucc, E.variable_cdfNode e.succ]
        simp only [OrderedMedium.gapLength, add_sub_cancel]
  have hs := E.geometry.integral_gap_sum hi
  rw [E.variable_source] at hs
  change (∑ e, ∫ t in (0 : ℝ)..E.geometry.gapLength e,
    f (E.geometry.node e.castSucc + t)) = ∫ x in (0 : ℝ)..1, f x at hs
  rw [← hs]
  exact Finset.sum_congr rfl (fun e _ => hlocal e)

theorem variable_mean_cdf_integral
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    (∫ x in (0 : ℝ)..1, E.state x) = (∑ i, E.partition.width i ^ 2 / E.strength i) +
      ∫ z in (0 : ℝ)..1,
        (1 / a z) * (E.geometry.absorptionCDF E.partition.width z - z) ^ 2 := by
  have he := variable_mean_energy E
  rw [← E.variable_weightedCDF_integral (variableMeanWeight a ha hapos)] at he
  simpa only [IntervalDesign.meanCost, variableUnitMedium, homogeneous,
    variableMeanWeight, sub_zero, div_one] using he

end TimeTraps.Interval
