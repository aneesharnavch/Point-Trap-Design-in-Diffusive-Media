module

public import TimeTraps.Interval.EndpointShares

@[expose] public section

/-! Reconstruction sites for an arbitrary strict mixed partition. Only
ordinary cells use balanced centers; reactive endpoint sites are fixed. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis

noncomputable def EndpointArchitecture.reconstructionSite (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) (i : Fin A.count) : ℝ :=
  match A.kind i with
  | .ordinary => Q.center W i
  | .leftEndpoint => 0
  | .rightEndpoint => 1

theorem EndpointArchitecture.reconstructionSite_ordinary (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) (i : Fin A.count)
    (hi : A.kind i = .ordinary) : A.reconstructionSite Q W i = Q.center W i := by
  simp only [reconstructionSite, hi]

theorem EndpointArchitecture.reconstructionSite_mem (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) (i : Fin A.count) :
    A.reconstructionSite Q W i ∈ Icc (Q.point i.castSucc) (Q.point i.succ) := by
  cases hi : A.kind i with
  | ordinary => simpa only [reconstructionSite, hi] using Ioo_subset_Icc_self (Q.center_mem W i)
  | leftEndpoint =>
    have he : i.castSucc = 0 := Fin.ext ((A.kind_left_iff i).mp hi).2
    simp only [reconstructionSite, hi, he, Q.first, left_mem_Icc]
    exact (Q.point_mem i.succ).1
  | rightEndpoint =>
    have he : i.succ = Fin.last A.count := Fin.ext ((A.kind_right_iff i).mp hi).2
    simp only [reconstructionSite, hi, he, Q.last, right_mem_Icc]
    exact (Q.point_mem i.castSucc).2

theorem EndpointArchitecture.reconstructionSite_strictMono (A : EndpointArchitecture)
    (Q : StrictPartition A.count) (W : CellWeight) : StrictMono (A.reconstructionSite Q W) := by
  intro i j hij
  have he : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
  have hr : A.reconstructionSite Q W i < Q.point i.succ := by
    cases hi : A.kind i with
    | ordinary => simpa only [reconstructionSite, hi] using (Q.center_mem W i).2
    | leftEndpoint =>
      have h0 : i.castSucc = 0 := Fin.ext ((A.kind_left_iff i).mp hi).2
      simpa only [reconstructionSite, hi, h0, Q.first] using Q.strictMono (Fin.castSucc_lt_succ (i := i))
    | rightEndpoint =>
      have hlast := ((A.kind_right_iff i).mp hi).2
      have hj := j.isLt
      have hij' : i.val < j.val := hij
      omega
  exact (hr.trans_le (Q.strictMono.monotone he)).trans_le (A.reconstructionSite_mem Q W j).1

theorem EndpointArchitecture.interiorCell_strictMono (A : EndpointArchitecture) :
    StrictMono A.interiorCell := by
  intro i j hij
  change A.leftReactive.toNat + i.val < A.leftReactive.toNat + j.val
  exact Nat.add_lt_add_left hij _

noncomputable def IntervalMedium.endpointPartitionGeometry (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) : OrderedMedium A.interiorCount :=
  OrderedMedium.ofSites B.source B.conductance B.conductance_continuous B.conductance_pos
    (fun j => B.partitionSites Q (A.interiorCell j))
    ((B.partitionSites_strictMono Q).comp A.interiorCell_strictMono)
    (fun j => B.partitionSites_interior Q (A.interiorCell j))

theorem IntervalMedium.endpointPartitionGeometry_medium (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) :
    (B.endpointPartitionGeometry A Q).medium = B := rfl

theorem IntervalMedium.endpointPartitionGeometry_site (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (j : Fin A.interiorCount) :
    (B.endpointPartitionGeometry A Q).site j = B.partitionSites Q (A.interiorCell j) :=
  OrderedMedium.ofSites_site _ _ _ _ _ _ _ j

theorem IntervalMedium.endpointPartitionGeometry_sourceSite (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (i : Fin A.count) :
    A.sourceSite (B.endpointPartitionGeometry A Q) i = A.reconstructionSite Q B.cellWeight i := by
  cases hi : A.kind i with
  | ordinary =>
    obtain ⟨j, rfl⟩ := A.ordinary_is_interiorCell i hi
    rw [A.sourceSite_interior, A.reconstructionSite_ordinary Q B.cellWeight _ hi]
    change B.source.coordinate ((B.endpointPartitionGeometry A Q).site j) = _
    rw [B.endpointPartitionGeometry_site]
    exact B.source.coordinate_inverse (Ioo_subset_Icc_self (Q.center_interior B.cellWeight _))
  | leftEndpoint => simp only [A.sourceSite_left _ _ hi, EndpointArchitecture.reconstructionSite, hi]
  | rightEndpoint => simp only [A.sourceSite_right _ _ hi, EndpointArchitecture.reconstructionSite, hi]

end TimeTraps.Interval
