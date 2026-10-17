module

public import TimeTraps.Analysis.SignedDirichletPointOperator
public import TimeTraps.Analysis.IntervalDirichletWeak

@[expose] public section

/-! The original signed Dirichlet/mixed operator graph is equivalent to
its physical integral equation against every H1 test with the selected
zero traces. No sign restriction is imposed on the contact strengths. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedDirichletPointProblem.load_representative (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalDirichletSpace P.boundary) :
    P.load f v = ∫ x in l..r, f x * v.val.representative P.boundary.interval_pos x :=
  intervalSobolevL2Load_representative P.boundary.interval_pos f v.val

theorem SignedDirichletPointProblem.load_ofEnergy (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {v : ℝ → ℝ} (hv : IntervalEnergy v l r)
    (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0) :
    P.load f (P.boundary.ofEnergy hv hvz) = ∫ x in l..r, f x * v x :=
  intervalSobolevL2Load_ofEnergy P.boundary.interval_pos f hv

theorem SignedDirichletPointProblem.weak_iff (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    (∀ v : IntervalDirichletSpace P.boundary,
      P.form (P.boundary.ofEnergy hu huz) v = inner ℝ f (P.boundary.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv hvz
    have he := h (P.boundary.ofEnergy hv hvz)
    change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hv hvz) =
      P.load f (P.boundary.ofEnergy hv hvz) at he
    rwa [intervalDirichletPointForm_ofEnergy, P.load_ofEnergy] at he
  · intro h v
    change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu huz) v = P.load f v
    rw [intervalDirichletPointForm_apply, P.load_representative]
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le
      P.site_mem (P.boundary.ofEnergy_representative hu huz) (fun _ _ => rfl)]
    exact h (v.val.representative P.boundary.interval_pos)
      (v.val.representative_spec P.boundary.interval_pos).1 (fun _ hx => P.boundary.representative_zero v hx)

theorem SignedDirichletPointProblem.operator_graph_iff_physical (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    (P.boundary.stateL (P.boundary.ofEnergy hu huz), f) ∈ P.operator.graph ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  rw [P.operator_graph_iff_state, P.weak_iff f hu huz]

theorem SignedDirichletPointProblem.operator_graph_iff_exists_physical
    (P : SignedDirichletPointProblem ι l r) (u f : IntervalSobolevL2 l r) :
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
