module

public import TimeTraps.Analysis.RegularSturmRegularityConverseGreen
public import TimeTraps.Analysis.RegularSturmRegularityPartition
public import TimeTraps.Analysis.RegularSturmRegularityPhysical

@[expose] public section

/-! Exact strong-domain characterization on any contact-containing
partition. Global H1 membership is derived from the closed-piece data;
the input state is only an L2 equivalence class. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : RegularSturmProblem ι l r} {n : ℕ}

theorem RegularSturmPartition.weak_of_fluxes (Q : RegularSturmPartition P n)
    (f : IntervalSobolevL2 l r) {U : ℝ → ℝ} (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - f x * Real.sqrt (P.speed x)) P.conductance
      (Q.point e.castSucc) (Q.point e.succ)) (ht : RegularSturmTransmission Q U j) :
    ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r U ψ = ∫ x in l..r, f x * Real.sqrt (P.speed x) * ψ x :=
  Q.weak_of_piecewise f (Q.energy_of_fluxes hj) j hj ht

theorem RegularSturmPartition.operator_graph_of_piecewise (Q : RegularSturmPartition P n)
    (u f : IntervalSobolevL2 l r) (U : ℝ → ℝ)
    (hu : u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x))
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - f x * Real.sqrt (P.speed x)) P.conductance
      (Q.point e.castSucc) (Q.point e.succ)) (ht : RegularSturmTransmission Q U j) :
    (u, f) ∈ P.operator.graph := by
  have hU := Q.energy_of_fluxes hj
  have he : u = P.stateL (P.boundary.ofEnergy hU ht.zero_boundary) :=
    Lp.ext (hu.trans (P.stateL_ofEnergy_ae hU ht.zero_boundary).symm)
  rw [he]
  exact (P.operator_graph_iff_physical f hU ht.zero_boundary).mpr (Q.weak_of_fluxes f j hj ht)

theorem RegularSturmPartition.operator_graph_iff_piecewise (Q : RegularSturmPartition P n)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔
      ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x) ∧
        (∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - f x * Real.sqrt (P.speed x)) P.conductance
          (Q.point e.castSucc) (Q.point e.succ)) ∧ RegularSturmTransmission Q U j := by
  constructor
  · intro hg
    obtain ⟨U, j, _, hu, hj, ht⟩ := Q.operator_graph_piecewise_regularity u f hg
    exact ⟨U, j, hu, hj, ht⟩
  · rintro ⟨U, j, hu, hj, ht⟩
    exact Q.operator_graph_of_piecewise u f U hu j hj ht

theorem RegularSturmPartition.operator_domain_iff_piecewise (Q : RegularSturmPartition P n)
    (u : IntervalSobolevL2 l r) :
    u ∈ P.operator.domain ↔
      ∃ (f : IntervalSobolevL2 l r) (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x) ∧
        (∀ e, IntervalFluxRegularity U (j e) (fun x => P.potential x * U x - f x * Real.sqrt (P.speed x)) P.conductance
          (Q.point e.castSucc) (Q.point e.succ)) ∧ RegularSturmTransmission Q U j := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [Q.operator_graph_iff_piecewise]

end TimeTraps.Analysis
