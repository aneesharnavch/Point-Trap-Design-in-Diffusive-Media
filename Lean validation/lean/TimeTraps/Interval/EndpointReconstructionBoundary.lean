module

public import TimeTraps.Interval.EndpointReconstructionProfile
public import TimeTraps.Interval.EndpointReconstructionReactions

@[expose] public section

/-! Exact endpoint absorption of the prescribed mixed source partition.
These identities also cover absent endpoints and endpoint-only designs. -/

namespace TimeTraps.Interval

theorem EndpointArchitecture.activeLift_width_left (A : EndpointArchitecture)
    (Q : StrictPartition A.count) :
    A.activeLift Q.width 0 = Q.point (A.gapBoundary 0) := by
  cases hl : A.leftReactive with
  | false =>
    rw [A.activeLift_left_zero Q.width hl]
    have he : A.gapBoundary 0 = 0 := by
      apply Fin.ext
      simp [gapBoundary, hl]
    rw [he, Q.first]
  | true =>
    let i : Fin A.count := ⟨0, A.count_pos⟩
    have hk : A.kind i = .leftEndpoint := (A.kind_left_iff i).mpr ⟨hl, rfl⟩
    rw [← A.activeNode_left i hk, A.activeLift_active]
    change Q.point i.succ - Q.point i.castSucc = Q.point (A.gapBoundary 0)
    rw [A.gapBoundary_left i hk]
    have he : i.castSucc = 0 := rfl
    rw [he, Q.first, sub_zero]

theorem EndpointArchitecture.activeLift_width_right (A : EndpointArchitecture)
    (Q : StrictPartition A.count) :
    A.activeLift Q.width (Fin.last (A.interiorCount + 1)) =
      1 - Q.point (A.gapBoundary (Fin.last A.interiorCount)) := by
  cases hr : A.rightReactive with
  | false =>
    rw [A.activeLift_right_zero Q.width hr]
    have he : A.gapBoundary (Fin.last A.interiorCount) = Fin.last A.count := by
      apply Fin.ext
      simp [gapBoundary, count, hr, Nat.add_comm]
    rw [he, Q.last, sub_self]
  | true =>
    let i : Fin A.count := ⟨A.count - 1, by have := A.count_pos; omega⟩
    have hi : i.val + 1 = A.count := by dsimp [i]; have := A.count_pos; omega
    have hk : A.kind i = .rightEndpoint := (A.kind_right_iff i).mpr ⟨hr, hi⟩
    rw [← A.activeNode_right i hk, A.activeLift_active]
    change Q.point i.succ - Q.point i.castSucc =
      1 - Q.point (A.gapBoundary (Fin.last A.interiorCount))
    rw [A.gapBoundary_right i hk]
    have he : i.succ = Fin.last A.count := Fin.ext hi
    rw [he, Q.last]

end TimeTraps.Interval
