module

public import TimeTraps.Analysis.GeneralIntervalPointRegularityConverseOperator
public import TimeTraps.Analysis.GeneralIntervalPointRegularityConstruction

@[expose] public section

/-! The actual operator domain has a finite piecewise H2 description for
every finite contact family. No ordered-partition existence premise or
independent global H1 assumption remains in these characterizations. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem IntervalPointProblem.operator_graph_iff_exists_partition (P : IntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔
      ∃ (n : ℕ) (Q : IntervalPointPartition P n) (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ IntervalPointTransmission Q U j := by
  constructor
  · intro hg
    obtain ⟨n, ⟨Q⟩⟩ := P.exists_partition
    obtain ⟨U, j, hu, hj, ht⟩ := (Q.operator_graph_iff_piecewise u f).mp hg
    exact ⟨n, Q, U, j, hu, hj, ht⟩
  · rintro ⟨n, Q, U, j, hu, hj, ht⟩
    exact Q.operator_graph_of_piecewise u f U hu j hj ht

theorem IntervalPointProblem.operator_domain_iff_exists_partition (P : IntervalPointProblem ι l r)
    (u : IntervalSobolevL2 l r) :
    u ∈ P.operator.domain ↔
      ∃ (f : IntervalSobolevL2 l r) (n : ℕ) (Q : IntervalPointPartition P n)
        (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ IntervalPointTransmission Q U j := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [P.operator_graph_iff_exists_partition]

end TimeTraps.Analysis
