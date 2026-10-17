module

public import TimeTraps.Interval.EndpointReflectionCell
public import TimeTraps.Interval.EndpointSelectable
public import Mathlib.Data.Fin.Rev

@[expose] public section

/-! Exact reversal of a closed source partition. Symmetric weights give
equal harmonic roots for the two single-reactive-endpoint architectures. -/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n m : ℕ}

def ClosedPartition.reflect (Q : ClosedPartition n) : ClosedPartition n :=
  ⟨fun e => 1 - Q.point e.rev,
    (by intro i j hij; exact sub_le_sub_left (Q.monotone (Fin.rev_le_rev.mpr hij)) 1),
    (by dsimp only; rw [Fin.rev_zero, Q.last]; ring),
    (by dsimp only; rw [Fin.rev_last, Q.first]; ring)⟩

theorem ClosedPartition.reflect_point (Q : ClosedPartition n) (e : Fin (n + 1)) :
    Q.reflect.point e = 1 - Q.point e.rev := rfl

theorem ClosedPartition.reflect_reflect (Q : ClosedPartition n) : Q.reflect.reflect = Q := by
  apply Subtype.ext
  funext e
  change 1 - (1 - Q.point e.rev.rev) = Q.point e
  rw [Fin.rev_rev]
  ring

theorem ClosedPartition.reflect_width (Q : ClosedPartition n) (i : Fin n) :
    Q.reflect.width i = Q.width i.rev := by
  simp only [ClosedPartition.width, Q.reflect_point, Fin.rev_succ, Fin.rev_castSucc]
  ring

theorem single_endpoint_reflect_kind (i : Fin (m + 1)) :
    (EndpointArchitecture.singleRight m).kind i =
      ((EndpointArchitecture.singleLeft m).kind i.rev).reflect := by
  have hi := i.isLt
  have hr : i.rev.val = m - i.val := by simp only [Fin.val_rev]; omega
  unfold EndpointArchitecture.kind EndpointArchitecture.singleRight EndpointArchitecture.singleLeft
  simp only [Bool.false_eq_true, false_and, ↓reduceIte, true_and,
    EndpointArchitecture.count, Bool.toNat_true, Bool.toNat_false, Nat.add_zero]
  by_cases h : i.val + 1 = m + 1
  · rw [if_pos h, if_pos (by omega : i.rev.val = 0)]
    rfl
  · rw [if_neg h, if_neg (by omega : i.rev.val ≠ 0)]
    rfl

theorem single_endpoint_reflect_barrier (Q : ClosedPartition (m + 1)) (W : CellWeight)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value (1 - z) = W.value z) (i : Fin (m + 1)) :
    (EndpointArchitecture.singleRight m).barrier Q.reflect W i =
      (EndpointArchitecture.singleLeft m).barrier Q W i.rev := by
  change W.orientedBarrier ((EndpointArchitecture.singleRight m).kind i)
    (1 - Q.point i.castSucc.rev) (1 - Q.point i.succ.rev) =
      W.orientedBarrier ((EndpointArchitecture.singleLeft m).kind i.rev)
        (Q.point i.rev.castSucc) (Q.point i.rev.succ)
  calc
    _ = W.orientedBarrier ((EndpointArchitecture.singleLeft m).kind i.rev).reflect
        (1 - Q.point i.rev.succ) (1 - Q.point i.rev.castSucc) := by
      exact (congrArg (fun kind => W.orientedBarrier kind
        (1 - Q.point i.castSucc.rev) (1 - Q.point i.succ.rev))
        (single_endpoint_reflect_kind i)).trans
        (congrArg₂ (W.orientedBarrier ((EndpointArchitecture.singleLeft m).kind i.rev).reflect)
          (congrArg (fun e => 1 - Q.point e) (Fin.rev_castSucc i))
          (congrArg (fun e => 1 - Q.point e) (Fin.rev_succ i)))
    _ = _ := W.orientedBarrier_reflect hW _ (Q.point_mem i.rev.castSucc).1
      (Q.point_mem i.rev.succ).2 (Q.monotone (Fin.castSucc_le_succ i.rev))

theorem single_endpoint_reflect_root (Q : ClosedPartition (m + 1)) (W : CellWeight)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value (1 - z) = W.value z)
    {b : ℝ} (hb : 0 < b) :
    (EndpointArchitecture.singleRight m).root Q.reflect W hb =
      (EndpointArchitecture.singleLeft m).root Q W hb := by
  apply ((EndpointArchitecture.singleRight m).eq_root Q.reflect W hb ?_ ?_).symm
  · intro i
    rw [single_endpoint_reflect_barrier Q W hW i]
    exact ((EndpointArchitecture.singleLeft m).root_spec Q W hb).1 i.rev
  · have h := ((EndpointArchitecture.singleLeft m).root_spec Q W hb).2
    change (∑ i : Fin (m + 1), Q.reflect.width i /
      ((EndpointArchitecture.singleLeft m).root Q W hb -
        (EndpointArchitecture.singleRight m).barrier Q.reflect W i)) = b
    calc
      _ = ∑ i : Fin (m + 1), Q.width i.rev /
          ((EndpointArchitecture.singleLeft m).root Q W hb -
            (EndpointArchitecture.singleLeft m).barrier Q W i.rev) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg₂ (fun p r : ℝ => p / ((EndpointArchitecture.singleLeft m).root Q W hb - r))
          (Q.reflect_width i) (single_endpoint_reflect_barrier Q W hW i)
      _ = ∑ i : Fin (m + 1), Q.width i /
          ((EndpointArchitecture.singleLeft m).root Q W hb -
            (EndpointArchitecture.singleLeft m).barrier Q W i) :=
        Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (m + 1)))
          (fun i => Q.width i / ((EndpointArchitecture.singleLeft m).root Q W hb -
            (EndpointArchitecture.singleLeft m).barrier Q W i))
      _ = b := h

end TimeTraps.Interval
