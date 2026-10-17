module

public import TimeTraps.Analysis.IntervalPointRegularityTransmission

@[expose] public section

/-! Actual solution and operator-graph consequences: piecewise H2
representatives and all signed transmission/endpoint laws, with no H1 or H2
regularity premise imposed on the input L2 graph element. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : UnitPointProblem ι} {n : ℕ}

theorem UnitPointPartition.weak_piecewise_regularity (Q : UnitPointPartition P n)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ 0 1 →
      unitPointForm P.diffusivity P.strength P.site u ψ = ∫ x in (0 : ℝ)..1, f x * ψ x) :
    ∃ j : Fin (n + 1) → ℝ → ℝ,
      (∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ UnitPointTransmission Q u j := by
  obtain ⟨j, hj⟩ := Q.local_slopes f hu hweak
  exact ⟨j, hj, Q.weak_transmission f hu hweak j hj⟩

theorem UnitPointPartition.solution_piecewise_regularity (Q : UnitPointPartition P n)
    (f : UnitIntervalL2) :
    ∃ j : Fin (n + 1) → ℝ → ℝ,
      (∀ e, IntervalSlopeRegularity ((P.solution f).representative zero_lt_one) (j e)
        (fun x => -f x / P.diffusivity) (Q.point e.castSucc) (Q.point e.succ)) ∧
      UnitPointTransmission Q ((P.solution f).representative zero_lt_one) j :=
  Q.weak_piecewise_regularity f ((P.solution f).representative_spec zero_lt_one).1
    (P.solution_physical f)

theorem UnitPointPartition.operator_graph_piecewise_regularity (Q : UnitPointPartition P n)
    (u f : UnitIntervalL2) (hg : (u, f) ∈ P.operator.graph) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U 0 1 ∧
      u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ UnitPointTransmission Q U j := by
  obtain ⟨j, hj, ht⟩ := Q.solution_piecewise_regularity f
  refine ⟨(P.solution f).representative zero_lt_one, j,
    ((P.solution f).representative_spec zero_lt_one).1, ?_, hj, ht⟩
  have he := P.operator_graph_iff u f |>.mp hg
  rw [← he, P.inverse_apply]
  exact ((P.solution f).representative_spec zero_lt_one).2.1

theorem UnitPointPartition.operator_domain_piecewise_regularity (Q : UnitPointPartition P n)
    (u : P.operator.domain) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U 0 1 ∧
      (u : UnitIntervalL2) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -(P.operator u) x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ UnitPointTransmission Q U j := by
  apply Q.operator_graph_piecewise_regularity (u : UnitIntervalL2) (P.operator u)
  rw [P.operator_graph_iff]
  exact inverseOperator_right_inverse P.inverse P.inverse_injective u

end TimeTraps.Analysis
