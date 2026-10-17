module

public import TimeTraps.Analysis.IntervalPeriodicRegularityConverseGreen
public import TimeTraps.Analysis.IntervalPeriodicRegularityPartition
public import TimeTraps.Analysis.IntervalPeriodicRegularityPhysical

@[expose] public section

/-! Exact strong-domain characterization on any contact-containing
partition. Global H1 membership is derived from the closed-piece data;
the input state is only an L2 equivalence class. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : PeriodicPointProblem ι l r} {n : ℕ}

theorem PeriodicPointPartition.weak_of_slopes (Q : PeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {U : ℝ → ℝ} (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (ht : PeriodicPointTransmission Q U j) :
    ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r → ψ l = ψ r →
      intervalPointForm P.diffusivity P.strength P.site l r U ψ = ∫ x in l..r, f x * ψ x :=
  Q.weak_of_piecewise f (Q.energy_of_slopes hj) j hj ht

theorem PeriodicPointPartition.operator_graph_of_piecewise (Q : PeriodicPointPartition P n)
    (u f : IntervalSobolevL2 l r) (U : ℝ → ℝ)
    (hu : u =ᵐ[volume.restrict (Ioo l r)] U)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (ht : PeriodicPointTransmission Q U j) :
    (u, f) ∈ P.operator.graph := by
  have hU := Q.energy_of_slopes hj
  have he : u = P.boundary.stateL (P.boundary.ofEnergy hU ht.periodic_state.symm) :=
    Lp.ext (hu.trans (P.boundary.ofEnergy_state_ae hU ht.periodic_state.symm).symm)
  rw [he]
  exact (P.operator_graph_iff_physical f hU ht.periodic_state).mpr (Q.weak_of_slopes f j hj ht)

theorem PeriodicPointPartition.operator_graph_iff_piecewise (Q : PeriodicPointPartition P n)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔
      ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ PeriodicPointTransmission Q U j := by
  constructor
  · intro hg
    obtain ⟨U, j, _, hu, hj, ht⟩ := Q.operator_graph_piecewise_regularity u f hg
    exact ⟨U, j, hu, hj, ht⟩
  · rintro ⟨U, j, hu, hj, ht⟩
    exact Q.operator_graph_of_piecewise u f U hu j hj ht

theorem PeriodicPointPartition.operator_domain_iff_piecewise (Q : PeriodicPointPartition P n)
    (u : IntervalSobolevL2 l r) :
    u ∈ P.operator.domain ↔
      ∃ (f : IntervalSobolevL2 l r) (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ PeriodicPointTransmission Q U j := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [Q.operator_graph_iff_piecewise]

end TimeTraps.Analysis
