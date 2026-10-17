module

public import TimeTraps.Interval.EndpointReflectionPartition

@[expose] public section

/-! A symmetric transformed profile gives equal attained physical minima
for a single reactive endpoint placed on either side. -/

namespace TimeTraps.Interval

open Set

variable {n m : ℕ} {K : ℝ}

def StrictPartition.reflect (Q : StrictPartition n) : StrictPartition n where
  point e := 1 - Q.point e.rev
  strictMono := by
    intro i j hij
    exact sub_lt_sub_left (Q.strictMono (Fin.rev_lt_rev.mpr hij)) 1
  first := by rw [Fin.rev_zero, Q.last]; ring
  last := by rw [Fin.rev_last, Q.first]; ring

theorem StrictPartition.reflect_closed (Q : StrictPartition n) :
    Q.reflect.closed = Q.closed.reflect := rfl

theorem single_endpoint_physical_values_equal (m : ℕ) (B : IntervalMedium) (hK : 0 < K)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value (1 - z) = B.cellWeight.value z) :
    (EndpointArchitecture.singleLeft m).physicalValue B K =
      (EndpointArchitecture.singleRight m).physicalValue B K := by
  obtain ⟨E, hE, he⟩ := (EndpointArchitecture.singleLeft m).physicalValue_attained B hK
  obtain ⟨F, hF, hf⟩ := (EndpointArchitecture.singleRight m).physicalValue_attained B hK
  rw [← he, ← hf]
  apply le_antisymm
  · have h := E.optimal_le_partition hE F.partition.reflect
    let Q : ClosedPartition (m + 1) := F.partition.closed
    change E.cost ≤ (EndpointArchitecture.singleLeft m).root Q.reflect B.cellWeight
      (div_pos hK B.source.mass_pos) at h
    have hr := single_endpoint_reflect_root Q.reflect B.cellWeight hW
      (div_pos hK B.source.mass_pos)
    have hd := congrArg (fun P : ClosedPartition (m + 1) =>
      (EndpointArchitecture.singleRight m).root P B.cellWeight (div_pos hK B.source.mass_pos))
      Q.reflect_reflect
    exact (h.trans_eq (hd.symm.trans hr).symm).trans_eq (F.optimal_cost_eq_root hF).symm
  · have h := F.optimal_le_partition hF E.partition.reflect
    change F.cost ≤ (EndpointArchitecture.singleRight m).root E.partition.closed.reflect B.cellWeight
      (div_pos hK B.source.mass_pos) at h
    exact (h.trans_eq (single_endpoint_reflect_root E.partition.closed B.cellWeight hW
      (div_pos hK B.source.mass_pos))).trans_eq (E.optimal_cost_eq_root hE).symm

theorem selectable_endpoint_symmetric_minimum (m : ℕ) (B : IntervalMedium) (hK : 0 < K)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value (1 - z) = B.cellWeight.value z) :
    IsLeast (range (fun E : EndpointAlternative (EndpointArchitecture.singleLeft m)
      (EndpointArchitecture.singleRight m) B K => E.cost))
      ((EndpointArchitecture.singleLeft m).physicalValue B K) := by
  have h := selectable_endpoint_minimum m B hK
  rw [← single_endpoint_physical_values_equal m B hK hW, min_self] at h
  exact h

end TimeTraps.Interval
