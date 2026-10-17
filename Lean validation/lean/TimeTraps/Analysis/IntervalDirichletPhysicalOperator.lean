module

public import TimeTraps.Analysis.IntervalDirichletWeak
public import TimeTraps.Analysis.IntervalDirichletOperator

@[expose] public section

/-! The actual absorbing-endpoint operator graph is exactly the original
weak equation with all zero-trace H1 tests and arbitrary L2 forcing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem DirichletPointProblem.operator_graph_iff_physical (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    (P.boundary.stateL (P.boundary.ofEnergy hu huz), f) ∈ P.operator.graph ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  rw [P.operator_graph_iff, P.inverse_eq_iff_weak f hu huz]

theorem DirichletPointProblem.operator_graph_iff_exists_physical
    (P : DirichletPointProblem ι l r) (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ U : ℝ → ℝ,
      IntervalEnergy U l r ∧ (∀ x ∈ P.boundary.zero_sites, U x = 0) ∧
      u =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r U v =
          ∫ x in l..r, f x * v x := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v.val.representative P.boundary.interval_pos,
      (v.val.representative_spec P.boundary.interval_pos).1,
      (fun _ hx => P.boundary.representative_zero v hx), ?_, ?_⟩
    · rw [← hv]
      exact (v.val.representative_spec P.boundary.interval_pos).2.1
    · apply (P.weak_iff f (v.val.representative_spec P.boundary.interval_pos).1
        (fun _ hx => P.boundary.representative_zero v hx)).mp
      rw [P.boundary.ofEnergy_representative_eq]
      exact he
  · rintro ⟨U, hU, hz, hu, he⟩
    refine ⟨P.boundary.ofEnergy hU hz, ?_, (P.weak_iff f hU hz).mpr he⟩
    exact Lp.ext ((P.boundary.ofEnergy_state_ae hU hz).trans hu.symm)


end TimeTraps.Analysis
