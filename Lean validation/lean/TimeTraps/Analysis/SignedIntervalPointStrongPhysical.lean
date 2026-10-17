module

public import TimeTraps.Analysis.SignedIntervalPointStrongTransmission

@[expose] public section

/-! Actual signed operator-graph consequences: piecewise H2
representatives and all signed transmission/endpoint laws, with no H1 or H2
regularity premise imposed on the input L2 graph element. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : SignedIntervalPointProblem ι l r} {n : ℕ}

theorem SignedIntervalPointPartition.weak_piecewise_regularity (Q : SignedIntervalPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x) :
    ∃ j : Fin (n + 1) → ℝ → ℝ,
      (∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedIntervalPointTransmission Q u j := by
  obtain ⟨j, hj⟩ := Q.local_slopes f hu hweak
  exact ⟨j, hj, Q.weak_transmission f hu hweak j hj⟩

theorem SignedIntervalPointPartition.operator_graph_piecewise_regularity (Q : SignedIntervalPointPartition P n)
    (u f : IntervalSobolevL2 l r) (hg : (u, f) ∈ P.operator.graph) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      u =ᵐ[volume.restrict (Ioo l r)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedIntervalPointTransmission Q U j := by
  obtain ⟨U, hU, hu, hweak⟩ := (P.operator_graph_iff_exists_physical u f).mp hg
  obtain ⟨j, hj, ht⟩ := Q.weak_piecewise_regularity f hU hweak
  exact ⟨U, j, hU, hu, hj, ht⟩

theorem SignedIntervalPointPartition.operator_domain_piecewise_regularity (Q : SignedIntervalPointPartition P n)
    (u : P.operator.domain) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      (u : IntervalSobolevL2 l r) =ᵐ[volume.restrict (Ioo l r)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -(P.operator u) x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedIntervalPointTransmission Q U j := by
  exact Q.operator_graph_piecewise_regularity (u : IntervalSobolevL2 l r) (P.operator u)
    (P.operator.mem_graph u)

end TimeTraps.Analysis
