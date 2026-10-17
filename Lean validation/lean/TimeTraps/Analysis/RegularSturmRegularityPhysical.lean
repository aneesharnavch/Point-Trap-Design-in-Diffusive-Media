module

public import TimeTraps.Analysis.RegularSturmRegularityTransmission

@[expose] public section

/-! Actual signed operator-graph consequences: piecewise AC flux
representatives and all signed transmission/endpoint laws, with no H1 or flux
regularity premise imposed on the input L2 graph element. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : RegularSturmProblem ι l r} {n : ℕ}

theorem RegularSturmPartition.weak_piecewise_regularity (Q : RegularSturmPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u ψ = ∫ x in l..r, f x * Real.sqrt (P.speed x) * ψ x) :
    ∃ j : Fin (n + 1) → ℝ → ℝ,
      (∀ e, IntervalFluxRegularity u (j e) (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) P.conductance
        (Q.point e.castSucc) (Q.point e.succ)) ∧ RegularSturmTransmission Q u j := by
  obtain ⟨j, hj⟩ := Q.local_fluxes f hu hweak
  exact ⟨j, hj, Q.weak_transmission f hu huz hweak j hj⟩

theorem RegularSturmPartition.operator_graph_piecewise_regularity (Q : RegularSturmPartition P n)
    (u f : IntervalSobolevL2 l r) (hg : (u, f) ∈ P.operator.graph) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x) ∧
      (∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - f x * Real.sqrt (P.speed x)) P.conductance
        (Q.point e.castSucc) (Q.point e.succ)) ∧ RegularSturmTransmission Q U j := by
  obtain ⟨U, hU, hz, hu, hw⟩ := (P.operator_graph_iff_exists_physical u f).mp hg
  obtain ⟨j, hj, ht⟩ := Q.weak_piecewise_regularity f hU hz hw
  exact ⟨U, j, hU, hu, hj, ht⟩

theorem RegularSturmPartition.operator_domain_piecewise_regularity (Q : RegularSturmPartition P n)
    (u : P.operator.domain) :
    ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ), IntervalEnergy U l r ∧
      (u : IntervalSobolevL2 l r) =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x) ∧
      (∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - (P.operator u) x * Real.sqrt (P.speed x)) P.conductance
        (Q.point e.castSucc) (Q.point e.succ)) ∧ RegularSturmTransmission Q U j := by
  apply Q.operator_graph_piecewise_regularity (u : IntervalSobolevL2 l r) (P.operator u)
  exact P.operator.mem_graph u

end TimeTraps.Analysis
