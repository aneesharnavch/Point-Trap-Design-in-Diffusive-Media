module

public import TimeTraps.Analysis.IntervalPointRegularityConverseOperator
public import TimeTraps.Analysis.IntervalPointRegularityConversePartition

@[expose] public section

/-! The actual operator domain has a finite piecewise H2 description for
every finite contact family. No ordered-partition existence premise or
independent global H1 assumption remains in these characterizations. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem UnitPointProblem.operator_graph_iff_exists_partition (P : UnitPointProblem ι)
    (u f : UnitIntervalL2) :
    (u, f) ∈ P.operator.graph ↔
      ∃ (n : ℕ) (Q : UnitPointPartition P n) (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ UnitPointTransmission Q U j := by
  constructor
  · intro hg
    obtain ⟨n, ⟨Q⟩⟩ := P.exists_partition
    obtain ⟨U, j, hu, hj, ht⟩ := (Q.operator_graph_iff_piecewise u f).mp hg
    exact ⟨n, Q, U, j, hu, hj, ht⟩
  · rintro ⟨n, Q, U, j, hu, hj, ht⟩
    exact Q.operator_graph_of_piecewise u f U hu j hj ht

theorem UnitPointProblem.operator_domain_iff_exists_partition (P : UnitPointProblem ι)
    (u : UnitIntervalL2) :
    u ∈ P.operator.domain ↔
      ∃ (f : UnitIntervalL2) (n : ℕ) (Q : UnitPointPartition P n)
        (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ UnitPointTransmission Q U j := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [P.operator_graph_iff_exists_partition]

end TimeTraps.Analysis
