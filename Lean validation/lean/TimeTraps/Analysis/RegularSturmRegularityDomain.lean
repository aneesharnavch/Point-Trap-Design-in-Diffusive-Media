module

public import TimeTraps.Analysis.RegularSturmRegularityConverseOperator
public import TimeTraps.Analysis.RegularSturmRegularityConstruction

@[expose] public section

/-! The actual operator domain has a finite piecewise AC flux description for
every finite contact family. No ordered-partition existence premise or
independent global H1 assumption remains in these characterizations. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem RegularSturmProblem.operator_graph_iff_exists_partition (P : RegularSturmProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔
      ∃ (n : ℕ) (Q : RegularSturmPartition P n) (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x) ∧
        (∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - f x * Real.sqrt (P.speed x)) P.conductance
          (Q.point e.castSucc) (Q.point e.succ)) ∧ RegularSturmTransmission Q U j := by
  constructor
  · intro hg
    obtain ⟨n, ⟨Q⟩⟩ := P.exists_partition
    obtain ⟨U, j, hu, hj, ht⟩ := (Q.operator_graph_iff_piecewise u f).mp hg
    exact ⟨n, Q, U, j, hu, hj, ht⟩
  · rintro ⟨n, Q, U, j, hu, hj, ht⟩
    exact Q.operator_graph_of_piecewise u f U hu j hj ht

theorem RegularSturmProblem.operator_domain_iff_exists_partition (P : RegularSturmProblem ι l r)
    (u : IntervalSobolevL2 l r) :
    u ∈ P.operator.domain ↔
      ∃ (f : IntervalSobolevL2 l r) (n : ℕ) (Q : RegularSturmPartition P n)
        (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x) ∧
        (∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - f x * Real.sqrt (P.speed x)) P.conductance
          (Q.point e.castSucc) (Q.point e.succ)) ∧ RegularSturmTransmission Q U j := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [P.operator_graph_iff_exists_partition]

end TimeTraps.Analysis
