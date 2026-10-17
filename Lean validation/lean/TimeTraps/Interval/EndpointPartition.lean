module

public import TimeTraps.Interval.EndpointArchitecture
public import TimeTraps.Interval.ClosedPartition

@[expose] public section

/-!
Mixed barriers on the closed source-partition simplex. The architecture is
fixed independently of all cell widths, including zero widths. The first
and last oriented cells use the actual one-sided endpoint integrals.
-/

namespace TimeTraps.Interval

open Set

noncomputable def EndpointArchitecture.barrier (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count) : ℝ :=
  W.orientedBarrier (A.kind i) (Q.point i.castSucc) (Q.point i.succ)

theorem EndpointArchitecture.barrier_nonneg (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count) :
    0 ≤ A.barrier Q W i :=
  W.orientedBarrier_nonneg (A.kind i) (Q.point_mem i.castSucc).1
    (Q.point_mem i.succ).2 (Q.monotone (Fin.castSucc_le_succ i))

theorem EndpointArchitecture.barrier_zero_iff_width_zero (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count) :
    A.barrier Q W i = 0 ↔ Q.width i = 0 := by
  rw [barrier, W.orientedBarrier_zero_iff (A.kind i) (Q.point_mem i.castSucc).1
    (Q.point_mem i.succ).2 (Q.monotone (Fin.castSucc_le_succ i))]
  unfold ClosedPartition.width
  exact eq_comm.trans sub_eq_zero.symm

theorem EndpointArchitecture.barrier_zero_of_width_zero (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count)
    (hi : Q.width i = 0) : A.barrier Q W i = 0 :=
  (A.barrier_zero_iff_width_zero Q W i).mpr hi

theorem EndpointArchitecture.barrier_pos_iff_width_pos (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count) :
    0 < A.barrier Q W i ↔ 0 < Q.width i := by
  constructor
  · intro hi
    have hn : Q.width i ≠ 0 := fun hz =>
      (ne_of_gt hi) (A.barrier_zero_of_width_zero Q W i hz)
    exact lt_of_le_of_ne (Q.width_nonneg i) hn.symm
  · intro hi
    exact W.orientedBarrier_pos (A.kind i) (Q.point_mem i.castSucc).1
      (Q.point_mem i.succ).2 (sub_pos.mp hi)

theorem EndpointArchitecture.barrier_continuous (A : EndpointArchitecture)
    (W : CellWeight) (i : Fin A.count) :
    Continuous (fun Q : ClosedPartition A.count => A.barrier Q W i) :=
  (W.orientedBarrier_continuous (A.kind i)).comp_continuous
    ((ClosedPartition.point_continuous i.castSucc).prodMk
      (ClosedPartition.point_continuous i.succ))
    (fun Q => ⟨(Q.point_mem i.castSucc).1,
      Q.monotone (Fin.castSucc_le_succ i), (Q.point_mem i.succ).2⟩)

theorem EndpointArchitecture.barrier_ordinary (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count)
    (hi : A.kind i = .ordinary) :
    A.barrier Q W i = W.barrier (Q.point i.castSucc) (Q.point i.succ) := by
  simp only [barrier, hi, CellWeight.orientedBarrier]

theorem EndpointArchitecture.barrier_interiorCell (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.interiorCount) :
    A.barrier Q W (A.interiorCell i) =
      W.barrier (Q.point (A.interiorCell i).castSucc) (Q.point (A.interiorCell i).succ) :=
  A.barrier_ordinary Q W _ (A.kind_interiorCell i)

theorem EndpointArchitecture.barrier_leftEndpoint (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count)
    (hi : A.kind i = .leftEndpoint) :
    A.barrier Q W i = W.rightRise (Q.width i) 0 := by
  have hzero : i.castSucc = 0 := Fin.ext ((A.kind_left_iff i).mp hi).2
  simp only [barrier, hi, CellWeight.orientedBarrier, ClosedPartition.width,
    hzero, Q.first, sub_zero]

theorem EndpointArchitecture.barrier_rightEndpoint (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count)
    (hi : A.kind i = .rightEndpoint) :
    A.barrier Q W i = W.leftRise (1 - Q.width i) 1 := by
  have hlast : i.succ = Fin.last A.count := Fin.ext ((A.kind_right_iff i).mp hi).2
  simp only [barrier, hi, CellWeight.orientedBarrier, ClosedPartition.width,
    hlast, Q.last, sub_sub_cancel]

theorem EndpointArchitecture.barrier_le_full (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (i : Fin A.count) :
    A.barrier Q W i ≤ W.orientedBarrier (A.kind i) 0 1 :=
  W.orientedBarrier_subcell_le (A.kind i) le_rfl le_rfl
    (Q.point_mem i.castSucc).1 (Q.monotone (Fin.castSucc_le_succ i))
    (Q.point_mem i.succ).2

end TimeTraps.Interval
