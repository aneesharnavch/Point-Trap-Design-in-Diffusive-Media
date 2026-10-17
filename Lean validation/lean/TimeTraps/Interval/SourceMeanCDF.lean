module

public import TimeTraps.Interval.SourceMeanEnergy

@[expose] public section

/-! The physical absorption CDF in source coordinates, including exact
integration across its jumps and the unsigned form of the position loss. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ} {A : IntervalMedium} {K : ℝ}

theorem source_mean_oriented_abs (W : CellWeight) (m x : ℝ) :
    (∫ t in m..x, W.value t * (t - m)) =
      ∫ t in min x m..max x m, W.value t * |t - m| := by
  by_cases hmx : m ≤ x
  · rw [min_eq_right hmx, max_eq_left hmx]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc m x := by simpa only [uIcc_of_le hmx] using ht
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr ht'.1)]
  · have hxm := le_of_not_ge hmx
    rw [min_eq_left hxm, max_eq_right hxm, weightedCDF_oriented_reverse]
    unfold CellWeight.rightRise
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc x m := by simpa only [uIcc_of_le hxm] using ht
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr ht'.2)]
    ring

theorem IntervalDesign.sourceCDF_on_gap (E : IntervalDesign A n K) (p : Fin n → ℝ)
    (e : Fin (n + 1)) {z : ℝ}
    (hz : z ∈ Ioo (cdfNode E.geometry.sourceSite e.castSucc) (cdfNode E.geometry.sourceSite e.succ)) :
    E.geometry.absorptionCDF p z = absorptionPrefix p e := by
  have hnode (v : Fin (n + 2)) : E.geometry.node v ∈ Icc A.source.left A.source.right := by
    rw [← E.source_eq]
    exact E.geometry.node_mem v
  rw [E.source_cdfNode e.castSucc, E.source_cdfNode e.succ] at hz
  have hz01 : z ∈ Icc (0 : ℝ) 1 :=
    ⟨(A.source.coordinate_mem (hnode e.castSucc)).1.trans hz.1.le,
      hz.2.le.trans (A.source.coordinate_mem (hnode e.succ)).2⟩
  have hl := A.source.inverse_strictMono (A.source.coordinate_mem (hnode e.castSucc)) hz01 hz.1
  have hr := A.source.inverse_strictMono hz01 (A.source.coordinate_mem (hnode e.succ)) hz.2
  rw [A.source.inverse_coordinate (hnode e.castSucc)] at hl
  rw [A.source.inverse_coordinate (hnode e.succ)] at hr
  have ht : A.source.inverse z - E.geometry.node e.castSucc ∈ Ioo 0 (E.geometry.gapLength e) := by
    constructor
    · exact sub_pos.mpr hl
    · exact sub_lt_sub_right hr _
  have he := E.geometry.absorptionCDF_gap p e ht
  rw [E.source_eq, add_sub_cancel, A.source.coordinate_inverse hz01] at he
  exact he

theorem IntervalDesign.source_weightedCDF_integral (E : IntervalDesign A n K) (W : CellWeight) :
    (∫ z in (0 : ℝ)..1, W.value z * (E.geometry.absorptionCDF E.partition.width z - z) ^ 2) =
      weightedCDFScore W E.partition.width E.geometry.sourceSite := by
  let f : ℝ → ℝ := fun z => W.value z * (E.geometry.absorptionCDF E.partition.width z - z) ^ 2
  let b := cdfNode E.geometry.sourceSite
  have hb (v : Fin (n + 2)) : b v ∈ Icc (0 : ℝ) 1 :=
    cdfNode_mem _ E.sourceSite_mem v
  have hs (e : Fin (n + 1)) : b e.castSucc ≤ b e.succ := by
    dsimp only [b]
    rw [E.source_cdfNode e.castSucc, E.source_cdfNode e.succ]
    have hnode (v : Fin (n + 2)) : E.geometry.node v ∈ Icc A.source.left A.source.right := by
      rw [← E.source_eq]
      exact E.geometry.node_mem v
    exact A.source.coordinate_strictMono.monotoneOn (hnode e.castSucc) (hnode e.succ)
      (E.geometry.node_strictMono Fin.castSucc_lt_succ).le
  have hlocal (e : Fin (n + 1)) : IntervalIntegrable f volume (b e.castSucc) (b e.succ) := by
    apply (weightedCDF_integrable W (absorptionPrefix E.partition.width e)
      (hb e.castSucc) (hb e.succ)).congr_uIoo
    intro z hz
    have hz' : z ∈ Ioo (b e.castSucc) (b e.succ) := by
      simpa only [uIoo_of_le (hs e)] using hz
    dsimp only [f]
    rw [E.sourceCDF_on_gap E.partition.width e hz']
  have hprefix (e : Fin (n + 1)) : IntervalIntegrable f volume (b 0) (b e.succ) := by
    induction e using Fin.induction with
    | zero => exact hlocal 0
    | succ i ih => exact ih.trans (hlocal i.succ)
  have hi : IntervalIntegrable f volume 0 1 := by
    have hh := hprefix (Fin.last n)
    change IntervalIntegrable f volume (cdfNode E.geometry.sourceSite 0)
      (cdfNode E.geometry.sourceSite (Fin.last (n + 1))) at hh
    simpa only [cdfNode_first, cdfNode_last] using hh
  have hiv (v : Fin (n + 2)) : IntervalIntegrable f volume 0 (b v) :=
    hi.mono_set (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le zero_le_one] using hb v))
  have hterm (e : Fin (n + 1)) :
      (∫ z in b e.castSucc..b e.succ, W.value z * (absorptionPrefix E.partition.width e - z) ^ 2) =
        (∫ z in (0 : ℝ)..b e.succ, f z) - (∫ z in (0 : ℝ)..b e.castSucc, f z) := by
    rw [intervalIntegral.integral_interval_sub_left (hiv e.succ) (hiv e.castSucc)]
    apply intervalIntegral.integral_congr_Ioo_of_le (hs e)
    intro z hz
    dsimp only [f]
    rw [E.sourceCDF_on_gap E.partition.width e hz]
  change (∫ z in (0 : ℝ)..1, f z) = ∑ e : Fin (n + 1),
    ∫ z in b e.castSucc..b e.succ, W.value z * (absorptionPrefix E.partition.width e - z) ^ 2
  simp_rw [hterm]
  rw [fin_sum_adjacent_difference (fun v => ∫ z in (0 : ℝ)..b v, f z)]
  simp only [b, cdfNode_first, cdfNode_last, intervalIntegral.integral_same, sub_zero]

theorem source_mean_cdf_integral (E : IntervalDesign A n K) :
    E.sourceMeanCost = A.source.mass * (∑ i, E.partition.width i ^ 2 / E.strength i) +
      ∫ z in (0 : ℝ)..1, A.cellWeight.value z * (E.geometry.absorptionCDF E.partition.width z - z) ^ 2 := by
  rw [E.source_weightedCDF_integral]
  exact source_mean_energy E

end TimeTraps.Interval
