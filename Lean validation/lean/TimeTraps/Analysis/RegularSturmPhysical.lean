module

public import TimeTraps.Analysis.RegularSturmPhysicalForm

@[expose] public section

/-! Both directions of the original full weak/operator graph for regular
Sturm data. The physical state has exactly the selected zero traces and
all such H1 functions are tests; conductance, speed and potential remain
continuous coefficients. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.weak_iff (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    (∀ v : IntervalSeparatedSpace P.boundary,
      P.form (P.boundary.ofEnergy hu huz) v = inner ℝ f (P.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
        ∫ x in l..r, f x * Real.sqrt (P.speed x) * v x) := by
  constructor
  · intro h v hv hvz
    have he := h (P.boundary.ofEnergy hv hvz)
    change P.form (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hv hvz) =
      P.load f (P.boundary.ofEnergy hv hvz) at he
    rwa [P.form_ofEnergy, P.load_ofEnergy f hv hvz] at he
  · intro h v
    change P.form (P.boundary.ofEnergy hu huz) v = P.load f v
    rw [P.form_apply, P.load_representative]
    rw [regularSturmPhysicalForm_congr P.conductance P.potential P.strength P.site
      P.boundary.interval_pos.le P.site_mem (P.boundary.ofEnergy_representative hu huz)
      (fun _ _ => rfl)]
    exact h (v.val.representative P.boundary.interval_pos)
      (v.val.representative_spec P.boundary.interval_pos).1
      (fun _ hx => P.boundary.representative_zero v hx)

theorem RegularSturmProblem.operator_graph_iff_physical (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    (P.stateL (P.boundary.ofEnergy hu huz), f) ∈ P.operator.graph ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
        ∫ x in l..r, f x * Real.sqrt (P.speed x) * v x) := by
  rw [P.operator_graph_iff_state, P.weak_iff f hu huz]

theorem RegularSturmProblem.operator_graph_iff_exists_physical
    (P : RegularSturmProblem ι l r) (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ U : ℝ → ℝ,
      IntervalEnergy U l r ∧ (∀ x ∈ P.boundary.zero_sites, U x = 0) ∧
      u =ᵐ[volume.restrict (Ioo l r)] (fun x => Real.sqrt (P.speed x) * U x) ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r → (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r U v =
          ∫ x in l..r, f x * Real.sqrt (P.speed x) * v x := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v.val.representative P.boundary.interval_pos,
      (v.val.representative_spec P.boundary.interval_pos).1,
      (fun _ hx => P.boundary.representative_zero v hx), ?_, ?_⟩
    · rw [← hv]
      exact P.stateL_representative_ae v
    · apply (P.weak_iff f (v.val.representative_spec P.boundary.interval_pos).1
        (fun _ hx => P.boundary.representative_zero v hx)).mp
      rw [P.boundary.ofEnergy_representative_eq]
      exact he
  · rintro ⟨U, hU, hz, hu, he⟩
    refine ⟨P.boundary.ofEnergy hU hz, ?_, (P.weak_iff f hU hz).mpr he⟩
    exact Lp.ext ((P.stateL_ofEnergy_ae hU hz).trans hu.symm)

end TimeTraps.Analysis
