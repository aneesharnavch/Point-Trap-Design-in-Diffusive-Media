module

public import TimeTraps.Interval.HomogeneousMeanEnergy

@[expose] public section

/-!
The finite gap score is the integral of the actual absorption CDF of a
homogeneous physical weak design. Affine change of variables is applied to
integrable gap pieces; no continuity of the step CDF at its jumps is assumed.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

theorem IntervalDesign.homogeneous_absorptionCDF
    (E : IntervalDesign (homogeneous L D hL hD) n K) (z : ℝ) :
    E.geometry.absorptionCDF E.partition.width z =
      ∑ i, if E.geometry.site i / L ≤ z then E.partition.width i else 0 := by
  unfold OrderedMedium.absorptionCDF OrderedMedium.sourceSite
  rw [E.homogeneous_source]
  simp only [homogeneous_coordinate]

theorem IntervalDesign.homogeneous_cdf_square_integral
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    (∫ z in (0 : ℝ)..1, (E.geometry.absorptionCDF E.partition.width z - z) ^ 2) =
      cdfSquareScore E.partition.width (fun i => E.geometry.site i / L) := by
  let f : ℝ → ℝ := fun z => (E.geometry.absorptionCDF E.partition.width z - z) ^ 2
  have hgap (e : Fin (n + 1)) {t : ℝ} (ht : t ∈ Ioo 0 (E.geometry.gapLength e)) :
      f ((E.geometry.node e.castSucc + t) / L) =
        (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t) / L) ^ 2 := by
    have hc := E.geometry.absorptionCDF_gap E.partition.width e ht
    rw [E.homogeneous_source, homogeneous_coordinate] at hc
    dsimp only [f]
    rw [hc]
  have hi : IntervalIntegrable (fun x => f (x / L)) volume
      E.geometry.source.left E.geometry.source.right := by
    apply E.geometry.integrable_of_gaps
    intro e
    have hp : IntervalIntegrable (fun t =>
        (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t) / L) ^ 2)
        volume 0 (E.geometry.gapLength e) := by
      apply Continuous.intervalIntegrable
      fun_prop
    apply hp.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) (E.geometry.gapLength e) := by
      simpa only [uIoo_of_le (E.geometry.gapLength_pos e).le] using ht
    exact (hgap e ht').symm
  have hlocal (e : Fin (n + 1)) :
      (∫ t in (0 : ℝ)..E.geometry.gapLength e,
        f ((E.geometry.node e.castSucc + t) / L)) =
      L * ∫ z in cdfNode (fun i => E.geometry.site i / L) e.castSucc..
        cdfNode (fun i => E.geometry.site i / L) e.succ,
        (absorptionPrefix E.partition.width e - z) ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..E.geometry.gapLength e,
          (absorptionPrefix E.partition.width e - (E.geometry.node e.castSucc + t) / L) ^ 2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (E.geometry.gapLength_pos e).le
        intro t ht
        exact hgap e ht
      _ = _ := by
        rw [E.homogeneous_cdfNode e.castSucc, E.homogeneous_cdfNode e.succ]
        exact integral_cdf_square_affine _ _ _ hL
  have hs := E.geometry.integral_gap_sum hi
  rw [E.homogeneous_source] at hs
  change (∑ e, ∫ t in (0 : ℝ)..E.geometry.gapLength e,
      f ((E.geometry.node e.castSucc + t) / L)) = ∫ x in (0 : ℝ)..L, f (x / L) at hs
  simp_rw [hlocal] at hs
  rw [← Finset.mul_sum, intervalIntegral.integral_comp_div _ (ne_of_gt hL),
    zero_div, div_self (ne_of_gt hL)] at hs
  change L * cdfSquareScore E.partition.width (fun i => E.geometry.site i / L) =
    L * ∫ z in (0 : ℝ)..1, f z at hs
  exact (mul_left_cancel₀ (ne_of_gt hL) hs).symm

theorem homogeneous_mean_cdf_integral
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    (∫ x in (0 : ℝ)..L, E.state x) / L =
      L * (∑ i, E.partition.width i ^ 2 / E.strength i) +
        L ^ 2 / D * ∫ z in (0 : ℝ)..1,
          (E.geometry.absorptionCDF E.partition.width z - z) ^ 2 := by
  rw [E.homogeneous_cdf_square_integral]
  exact homogeneous_mean_energy E

end TimeTraps.Interval
