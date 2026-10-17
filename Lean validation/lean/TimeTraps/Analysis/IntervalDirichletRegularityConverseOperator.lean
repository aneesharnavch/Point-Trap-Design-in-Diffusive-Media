module

public import TimeTraps.Analysis.IntervalDirichletRegularityConverseGreen
public import TimeTraps.Analysis.IntervalDirichletRegularityPartition
public import TimeTraps.Analysis.IntervalDirichletRegularityPhysical

@[expose] public section

/-! Exact strong-domain characterization on any contact-containing
partition. Global H1 membership is derived from the closed-piece data;
the input state is only an L2 equivalence class. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : DirichletPointProblem ι l r} {n : ℕ}

theorem DirichletPointPartition.weak_of_slopes (Q : DirichletPointPartition P n)
    (f : IntervalSobolevL2 l r) {U : ℝ → ℝ} (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (ht : DirichletPointTransmission Q U j) :
    ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r U ψ = ∫ x in l..r, f x * ψ x :=
  Q.weak_of_piecewise f (Q.energy_of_slopes hj) j hj ht

theorem DirichletPointPartition.operator_graph_of_piecewise (Q : DirichletPointPartition P n)
    (u f : IntervalSobolevL2 l r) (U : ℝ → ℝ)
    (hu : u =ᵐ[volume.restrict (Ioo l r)] U)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (ht : DirichletPointTransmission Q U j) :
    (u, f) ∈ P.operator.graph := by
  have hU := Q.energy_of_slopes hj
  have he : u = P.boundary.stateL (P.boundary.ofEnergy hU ht.zero_boundary) :=
    Lp.ext (hu.trans (P.boundary.ofEnergy_state_ae hU ht.zero_boundary).symm)
  rw [he]
  exact (P.operator_graph_iff_physical f hU ht.zero_boundary).mpr (Q.weak_of_slopes f j hj ht)

theorem DirichletPointPartition.operator_graph_iff_piecewise (Q : DirichletPointPartition P n)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔
      ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ DirichletPointTransmission Q U j := by
  constructor
  · intro hg
    obtain ⟨U, j, _, hu, hj, ht⟩ := Q.operator_graph_piecewise_regularity u f hg
    exact ⟨U, j, hu, hj, ht⟩
  · rintro ⟨U, j, hu, hj, ht⟩
    exact Q.operator_graph_of_piecewise u f U hu j hj ht

theorem DirichletPointPartition.operator_domain_iff_piecewise (Q : DirichletPointPartition P n)
    (u : IntervalSobolevL2 l r) :
    u ∈ P.operator.domain ↔
      ∃ (f : IntervalSobolevL2 l r) (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ DirichletPointTransmission Q U j := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [Q.operator_graph_iff_piecewise]

end TimeTraps.Analysis
