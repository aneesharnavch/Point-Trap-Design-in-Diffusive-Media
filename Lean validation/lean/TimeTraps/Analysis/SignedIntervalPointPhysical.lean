module

public import TimeTraps.Analysis.SignedIntervalPointUnshifted

@[expose] public section

/-! The unshifted signed operator is exactly the original physical point
form against all H1 tests. The auxiliary coercivity shift has canceled;
no nonnegativity of strengths or nonzero contact count is required. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.weak_iff (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    (∀ v : IntervalSobolevSpace l r,
      P.form (ofEnergy hu P.interval_pos) v = inner ℝ f v.state) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv
    have he := h (ofEnergy hv P.interval_pos)
    change intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem
      (ofEnergy hu P.interval_pos) (ofEnergy hv P.interval_pos) =
      intervalSobolevL2Load l r f (ofEnergy hv P.interval_pos) at he
    rwa [intervalSobolevPointForm_ofEnergy, intervalSobolevL2Load_ofEnergy] at he
  · intro h v
    change intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem
      (ofEnergy hu P.interval_pos) v = intervalSobolevL2Load l r f v
    rw [intervalSobolevPointForm_apply, intervalSobolevL2Load_representative P.interval_pos]
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.interval_pos.le P.site_mem
      (representative_ofEnergy hu P.interval_pos) (fun _ _ => rfl)]
    exact h (v.representative P.interval_pos) (v.representative_spec P.interval_pos).1

theorem SignedIntervalPointProblem.operator_graph_iff_physical (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    ((ofEnergy hu P.interval_pos).state, f) ∈ P.operator.graph ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x := by
  rw [P.operator_graph_iff_state, P.weak_iff f hu]

theorem SignedIntervalPointProblem.operator_graph_iff_exists_physical
    (P : SignedIntervalPointProblem ι l r) (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ U : ℝ → ℝ,
      IntervalEnergy U l r ∧ u =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r U v = ∫ x in l..r, f x * v x := by
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := (P.operator_graph_iff_hilbert u f).mp h
    refine ⟨v.representative P.interval_pos, (v.representative_spec P.interval_pos).1, ?_, ?_⟩
    · rw [← hv]
      exact (v.representative_spec P.interval_pos).2.1
    · apply (P.weak_iff f (v.representative_spec P.interval_pos).1).mp
      rwa [ofEnergy_representative]
  · rintro ⟨U, hU, hu, he⟩
    have hs : (ofEnergy hU P.interval_pos).state = u :=
      Lp.ext ((ofEnergy_spec hU P.interval_pos).1.trans hu.symm)
    have hg := (P.operator_graph_iff_physical f hU).mpr he
    rwa [hs] at hg

end TimeTraps.Analysis
