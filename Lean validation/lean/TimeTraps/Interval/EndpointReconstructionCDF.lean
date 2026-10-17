module

public import TimeTraps.Interval.EndpointReconstructionGeometry
public import TimeTraps.Interval.PartitionCDF

@[expose] public section

/-! The prescribed mixed absorption CDF and its exact cell values. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped BigOperators Classical Topology

noncomputable def EndpointArchitecture.reconstructionCDF (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) (z : ℝ) : ℝ :=
  ∑ i, if A.reconstructionSite Q W i ≤ z then Q.width i else 0

theorem EndpointArchitecture.reconstructionCDF_integrable (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) (a b : ℝ) :
    IntervalIntegrable (A.reconstructionCDF Q W) volume a b := by
  have hi : ∀ i : Fin A.count, IntervalIntegrable
      (fun z => if A.reconstructionSite Q W i ≤ z then Q.width i else 0) volume a b := by
    intro i
    have hc : IntervalIntegrable (fun _ : ℝ => Q.width i) volume a b := intervalIntegrable_const
    have he : (Ici (A.reconstructionSite Q W i)).indicator (fun _ : ℝ => Q.width i) =
        (fun z => if A.reconstructionSite Q W i ≤ z then Q.width i else 0) := by
      funext z
      simp only [Set.indicator, mem_Ici]
    constructor
    · rw [← he]; exact hc.1.indicator measurableSet_Ici
    · rw [← he]; exact hc.2.indicator measurableSet_Ici
  have hs := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
  have he : (∑ i : Fin A.count, fun z => if A.reconstructionSite Q W i ≤ z then Q.width i else 0) =
      A.reconstructionCDF Q W := by funext z; simp only [reconstructionCDF, Finset.sum_apply]
  rwa [he] at hs

theorem EndpointArchitecture.reconstructionCDF_measurable (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) : Measurable (A.reconstructionCDF Q W) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem EndpointArchitecture.reconstructionCDF_continuousAt (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) {z : ℝ}
    (hz : ∀ i, A.reconstructionSite Q W i ≠ z) : ContinuousAt (A.reconstructionCDF Q W) z := by
  apply tendsto_finsetSum
  intro i _
  rcases lt_or_gt_of_ne (hz i) with hi | hi
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => Q.width i) z).congr
    filter_upwards [isOpen_Ioi.mem_nhds hi] with t ht
    change A.reconstructionSite Q W i < t at ht
    simp only [if_pos ht.le]
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) z).congr
    filter_upwards [isOpen_Iio.mem_nhds hi] with t ht
    change t < A.reconstructionSite Q W i at ht
    simp only [if_neg (not_le.mpr ht)]

theorem EndpointArchitecture.reconstructionCDF_left (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) (i : Fin A.count) {z : ℝ}
    (hz : z ∈ Ioo (Q.point i.castSucc) (A.reconstructionSite Q W i)) :
    A.reconstructionCDF Q W z = Q.point i.castSucc := by
  rw [← Q.prefix_width i.castSucc]
  unfold reconstructionCDF absorptionPrefix
  apply Finset.sum_congr rfl
  intro k _
  have hi : A.reconstructionSite Q W k ≤ z ↔ k.val < i.val := by
    constructor
    · intro h
      by_contra hki
      have hik : i ≤ k := by change i.val ≤ k.val; omega
      have hc := (A.reconstructionSite_strictMono Q W).monotone hik
      linarith [hz.2]
    · intro hki
      have hk : k.succ ≤ i.castSucc := by change k.val + 1 ≤ i.val; omega
      exact ((A.reconstructionSite_mem Q W k).2.trans (Q.strictMono.monotone hk)).trans hz.1.le
  simp only [hi, Fin.val_castSucc]

theorem EndpointArchitecture.reconstructionCDF_right (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) (i : Fin A.count) {z : ℝ}
    (hz : z ∈ Ioo (A.reconstructionSite Q W i) (Q.point i.succ)) :
    A.reconstructionCDF Q W z = Q.point i.succ := by
  rw [← Q.prefix_width i.succ]
  unfold reconstructionCDF absorptionPrefix
  apply Finset.sum_congr rfl
  intro k _
  have hi : A.reconstructionSite Q W k ≤ z ↔ k.val < i.val + 1 := by
    constructor
    · intro h
      by_contra hki
      have hik : i.succ ≤ k.castSucc := by change i.val + 1 ≤ k.val; omega
      have hc := Q.strictMono.monotone hik
      linarith [(A.reconstructionSite_mem Q W k).1, hz.2]
    · intro hki
      have hk : k ≤ i := by change k.val ≤ i.val; omega
      exact ((A.reconstructionSite_strictMono Q W).monotone hk).trans hz.1.le
  simp only [hi, Fin.val_succ]

noncomputable def IntervalMedium.endpointPartitionSlope (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (z : ℝ) : ℝ :=
  B.source.weight B.conductance z * (A.reconstructionCDF Q B.cellWeight z - z)

theorem IntervalMedium.endpointPartitionSlope_integrable (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (a b : ℝ) :
    IntervalIntegrable (B.endpointPartitionSlope A Q) volume a b :=
  ((A.reconstructionCDF_integrable Q B.cellWeight a b).sub
    (continuous_id.intervalIntegrable a b)).continuousOn_mul
      (B.source.weight_continuous B.conductance_continuous B.conductance_pos).continuousOn

theorem IntervalMedium.endpointPartitionSlope_measurable (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) :
    Measurable (B.endpointPartitionSlope A Q) :=
  (B.source.weight_continuous B.conductance_continuous B.conductance_pos).measurable.mul
    ((A.reconstructionCDF_measurable Q B.cellWeight).sub measurable_id)

theorem IntervalMedium.endpointPartitionSlope_continuousAt (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {z : ℝ}
    (hz : ∀ i, A.reconstructionSite Q B.cellWeight i ≠ z) :
    ContinuousAt (B.endpointPartitionSlope A Q) z :=
  (B.source.weight_continuous B.conductance_continuous B.conductance_pos).continuousAt.mul
    ((A.reconstructionCDF_continuousAt Q B.cellWeight hz).sub continuousAt_id)

end TimeTraps.Interval
