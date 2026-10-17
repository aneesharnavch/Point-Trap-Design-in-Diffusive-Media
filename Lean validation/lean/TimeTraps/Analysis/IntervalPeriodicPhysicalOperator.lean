module

public import TimeTraps.Analysis.IntervalPeriodicWeak
public import TimeTraps.Analysis.IntervalPeriodicOperator

@[expose] public section

/-! The actual periodic operator graph is exactly the full physical
weak equation with matching endpoint traces and arbitrary L2 forcing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem PeriodicPointProblem.operator_graph_iff_physical (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hup : u l = u r) :
    (P.boundary.stateL (P.boundary.ofEnergy hu hup.symm), f) ∈ P.operator.graph ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → v l = v r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  rw [P.operator_graph_iff, P.inverse_eq_iff_weak f hu hup]

theorem PeriodicPointProblem.operator_graph_iff_exists_physical
    (P : PeriodicPointProblem ι l r) (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ U : ℝ → ℝ,
      IntervalEnergy U l r ∧ U l = U r ∧
      u =ᵐ[volume.restrict (Ioo l r)] U ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r → v l = v r →
        intervalPointForm P.diffusivity P.strength P.site l r U v =
          ∫ x in l..r, f x * v x := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v.val.representative P.boundary.interval_pos,
      (v.val.representative_spec P.boundary.interval_pos).1,
      (P.boundary.representative_periodic v).symm, ?_, ?_⟩
    · rw [← hv]
      exact (v.val.representative_spec P.boundary.interval_pos).2.1
    · apply (P.weak_iff f (v.val.representative_spec P.boundary.interval_pos).1
        (P.boundary.representative_periodic v).symm).mp
      rw [P.boundary.ofEnergy_representative_eq]
      exact he
  · rintro ⟨U, hU, hp, hu, he⟩
    refine ⟨P.boundary.ofEnergy hU hp.symm, ?_, (P.weak_iff f hU hp).mpr he⟩
    exact Lp.ext ((P.boundary.ofEnergy_state_ae hU hp.symm).trans hu.symm)

end TimeTraps.Analysis
