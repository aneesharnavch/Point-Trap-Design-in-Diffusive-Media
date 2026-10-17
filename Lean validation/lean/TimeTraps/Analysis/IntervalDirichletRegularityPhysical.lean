module

public import TimeTraps.Analysis.IntervalDirichletRegularityTransmission

@[expose] public section

/-! Actual solution and operator-graph consequences: piecewise H2
representatives and all signed transmission/endpoint laws, with no H1 or H2
regularity premise imposed on the input L2 graph element. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : DirichletPointProblem ι l r} {n : ℕ}

theorem DirichletPointPartition.weak_piecewise_regularity (Q : DirichletPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x) :
    ∃ j : Fin (n + 1) → ℝ → ℝ,
      (∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ DirichletPointTransmission Q u j := by
  obtain ⟨j, hj⟩ := Q.local_slopes f hu hweak
  exact ⟨j, hj, Q.weak_transmission f hu huz hweak j hj⟩

theorem DirichletPointPartition.solution_piecewise_regularity (Q : DirichletPointPartition P n)
    (f : IntervalSobolevL2 l r) :
    ∃ j : Fin (n + 1) → ℝ → ℝ,
      (∀ e, IntervalSlopeRegularity ((P.solution f).val.representative P.boundary.interval_pos) (j e)
        (fun x => -f x / P.diffusivity) (Q.point e.castSucc) (Q.point e.succ)) ∧
      DirichletPointTransmission Q ((P.solution f).val.representative P.boundary.interval_pos) j :=
  Q.weak_piecewise_regularity f ((P.solution f).val.representative_spec P.boundary.interval_pos).1
    (fun _ hx => P.boundary.representative_zero (P.solution f) hx)
    (P.solution_physical f)

theorem DirichletPointPartition.operator_graph_piecewise_regularity (Q : DirichletPointPartition P n)
    (u f : IntervalSobolevL2 l r) (hg : (u, f) ∈ P.operator.graph) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      u =ᵐ[volume.restrict (Ioo l r)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ DirichletPointTransmission Q U j := by
  obtain ⟨j, hj, ht⟩ := Q.solution_piecewise_regularity f
  refine ⟨(P.solution f).val.representative P.boundary.interval_pos, j,
    ((P.solution f).val.representative_spec P.boundary.interval_pos).1, ?_, hj, ht⟩
  have he := P.operator_graph_iff u f |>.mp hg
  rw [← he, P.inverse_apply]
  exact ((P.solution f).val.representative_spec P.boundary.interval_pos).2.1

theorem DirichletPointPartition.operator_domain_piecewise_regularity (Q : DirichletPointPartition P n)
    (u : P.operator.domain) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      (u : IntervalSobolevL2 l r) =ᵐ[volume.restrict (Ioo l r)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -(P.operator u) x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ DirichletPointTransmission Q U j := by
  apply Q.operator_graph_piecewise_regularity (u : IntervalSobolevL2 l r) (P.operator u)
  rw [P.operator_graph_iff]
  exact inverseOperator_right_inverse P.inverse P.inverse_injective u

end TimeTraps.Analysis
