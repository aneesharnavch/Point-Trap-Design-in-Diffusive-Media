module

public import TimeTraps.Analysis.SignedPeriodicPointRegularityTransmission

@[expose] public section

/-! Actual signed operator-graph consequences: piecewise H2
representatives and all signed transmission/endpoint laws, with no H1 or H2
regularity premise imposed on the input L2 graph element. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : SignedPeriodicPointProblem ι l r} {n : ℕ}

theorem SignedPeriodicPointPartition.weak_piecewise_regularity (Q : SignedPeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hup : u l = u r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r → ψ l = ψ r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x) :
    ∃ j : Fin (n + 1) → ℝ → ℝ,
      (∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedPeriodicPointTransmission Q u j := by
  obtain ⟨j, hj⟩ := Q.local_slopes f hu hweak
  exact ⟨j, hj, Q.weak_transmission f hu hup hweak j hj⟩

theorem SignedPeriodicPointPartition.operator_graph_piecewise_regularity (Q : SignedPeriodicPointPartition P n)
    (u f : IntervalSobolevL2 l r) (hg : (u, f) ∈ P.operator.graph) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      u =ᵐ[volume.restrict (Ioo l r)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedPeriodicPointTransmission Q U j := by
  obtain ⟨U, hU, hp, hu, hw⟩ := (P.operator_graph_iff_exists_physical u f).mp hg
  obtain ⟨j, hj, ht⟩ := Q.weak_piecewise_regularity f hU hp hw
  exact ⟨U, j, hU, hu, hj, ht⟩

theorem SignedPeriodicPointPartition.operator_domain_piecewise_regularity (Q : SignedPeriodicPointPartition P n)
    (u : P.operator.domain) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      (u : IntervalSobolevL2 l r) =ᵐ[volume.restrict (Ioo l r)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e) (fun x => -(P.operator u) x / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedPeriodicPointTransmission Q U j := by
  apply Q.operator_graph_piecewise_regularity (u : IntervalSobolevL2 l r) (P.operator u)
  exact P.operator.mem_graph u

end TimeTraps.Analysis
