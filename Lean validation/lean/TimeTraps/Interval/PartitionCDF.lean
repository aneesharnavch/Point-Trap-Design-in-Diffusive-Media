module

public import TimeTraps.Interval.StrictPartition

@[expose] public section

/-!
The prescribed absorption CDF for balanced partition sites. Its values on
both halves of each cell follow from the independent order data.
-/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped BigOperators Classical Topology

variable {n : ℕ}

theorem OrderedMedium.absorptionCDF_measurable (D : OrderedMedium n) (p : Fin n → ℝ) :
    Measurable (D.absorptionCDF p) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem OrderedMedium.absorptionCDF_continuousAt (D : OrderedMedium n) (p : Fin n → ℝ)
    {z : ℝ} (hz : ∀ i, D.sourceSite i ≠ z) : ContinuousAt (D.absorptionCDF p) z := by
  apply tendsto_finsetSum
  intro i _
  rcases lt_or_gt_of_ne (hz i) with hi | hi
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => p i) z).congr
    filter_upwards [isOpen_Ioi.mem_nhds hi] with t ht
    change D.sourceSite i < t at ht
    simp only [if_pos (le_of_lt ht)]
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) z).congr
    filter_upwards [isOpen_Iio.mem_nhds hi] with t ht
    change t < D.sourceSite i at ht
    simp only [if_neg (not_le.mpr ht)]

theorem IntervalMedium.partitionCDF_left (A : IntervalMedium) (Q : StrictPartition n) (i : Fin n)
    {z : ℝ} (hz : z ∈ Ioo (Q.point i.castSucc) (Q.center A.cellWeight i)) :
    (A.partitionDesign Q).absorptionCDF Q.width z = Q.point i.castSucc := by
  rw [← Q.prefix_width i.castSucc]
  unfold OrderedMedium.absorptionCDF absorptionPrefix
  apply Finset.sum_congr rfl
  intro k _
  rw [A.partitionDesign_sourceSite]
  have hi : Q.center A.cellWeight k ≤ z ↔ k.val < i.val := by
    constructor
    · intro h
      by_contra hki
      have hik : i ≤ k := by change i.val ≤ k.val; omega
      have hc := (Q.center_strictMono A.cellWeight).monotone hik
      linarith [hz.2]
    · intro hki
      have hk : k.succ ≤ i.castSucc := by change k.val + 1 ≤ i.val; omega
      exact (((Q.center_mem A.cellWeight k).2).trans_le (Q.strictMono.monotone hk)).le.trans hz.1.le
  simp only [hi, Fin.val_castSucc]

theorem IntervalMedium.partitionCDF_right (A : IntervalMedium) (Q : StrictPartition n) (i : Fin n)
    {z : ℝ} (hz : z ∈ Ioo (Q.center A.cellWeight i) (Q.point i.succ)) :
    (A.partitionDesign Q).absorptionCDF Q.width z = Q.point i.succ := by
  rw [← Q.prefix_width i.succ]
  unfold OrderedMedium.absorptionCDF absorptionPrefix
  apply Finset.sum_congr rfl
  intro k _
  rw [A.partitionDesign_sourceSite]
  have hi : Q.center A.cellWeight k ≤ z ↔ k.val < i.val + 1 := by
    constructor
    · intro h
      by_contra hki
      have hik : i.succ ≤ k.castSucc := by change i.val + 1 ≤ k.val; omega
      have hc := Q.strictMono.monotone hik
      linarith [(Q.center_mem A.cellWeight k).1, hz.2]
    · intro hki
      have hk : k ≤ i := by change k.val ≤ i.val; omega
      exact ((Q.center_strictMono A.cellWeight).monotone hk).trans hz.1.le
  simp only [hi, Fin.val_succ]

noncomputable def IntervalMedium.partitionSlope (A : IntervalMedium) (Q : StrictPartition n)
    (z : ℝ) : ℝ := A.source.weight A.conductance z *
      ((A.partitionDesign Q).absorptionCDF Q.width z - z)

theorem IntervalMedium.partitionSlope_integrable (A : IntervalMedium) (Q : StrictPartition n)
    (a b : ℝ) : IntervalIntegrable (A.partitionSlope Q) volume a b := by
  exact (((A.partitionDesign Q).absorptionCDF_integrable Q.width a b).sub
    (continuous_id.intervalIntegrable a b)).continuousOn_mul
      (A.source.weight_continuous A.conductance_continuous A.conductance_pos).continuousOn

theorem IntervalMedium.partitionSlope_measurable (A : IntervalMedium) (Q : StrictPartition n) :
    Measurable (A.partitionSlope Q) :=
  (A.source.weight_continuous A.conductance_continuous A.conductance_pos).measurable.mul
    (((A.partitionDesign Q).absorptionCDF_measurable Q.width).sub measurable_id)

theorem IntervalMedium.partitionSlope_continuousAt (A : IntervalMedium) (Q : StrictPartition n)
    {z : ℝ} (hz : ∀ i, Q.center A.cellWeight i ≠ z) : ContinuousAt (A.partitionSlope Q) z := by
  apply (A.source.weight_continuous A.conductance_continuous A.conductance_pos).continuousAt.mul
  apply ContinuousAt.sub ?_ continuousAt_id
  exact (A.partitionDesign Q).absorptionCDF_continuousAt Q.width
    (fun i => by simpa only [A.partitionDesign_sourceSite] using hz i)

end TimeTraps.Interval
