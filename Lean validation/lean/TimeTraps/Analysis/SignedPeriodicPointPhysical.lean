module

public import TimeTraps.Analysis.SignedPeriodicPointOperator
public import TimeTraps.Analysis.IntervalPeriodicWeak

@[expose] public section

/-! The original arbitrary-real-contact periodic operator is equivalent
 to its full physical weak equation with matching endpoint values. Both
 endpoint labels contribute at the same seam; no endpoint value is fixed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.load_representative (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalPeriodicSpace P.boundary) :
    P.load f v = ∫ x in l..r, f x * v.val.representative P.boundary.interval_pos x :=
  intervalSobolevL2Load_representative P.boundary.interval_pos f v.val

theorem SignedPeriodicPointProblem.load_ofEnergy (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {v : ℝ → ℝ} (hv : IntervalEnergy v l r)
    (hvp : v l = v r) :
    P.load f (P.boundary.ofEnergy hv hvp.symm) = ∫ x in l..r, f x * v x :=
  intervalSobolevL2Load_ofEnergy P.boundary.interval_pos f hv

theorem SignedPeriodicPointProblem.weak_iff (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hup : u l = u r) :
    (∀ v : IntervalPeriodicSpace P.boundary,
      P.form (P.boundary.ofEnergy hu hup.symm) v = inner ℝ f (P.boundary.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → v l = v r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  constructor
  · intro h v hv hvp
    have he := h (P.boundary.ofEnergy hv hvp.symm)
    change intervalPeriodicPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu hup.symm) (P.boundary.ofEnergy hv hvp.symm) =
      P.load f (P.boundary.ofEnergy hv hvp.symm) at he
    rwa [intervalPeriodicPointForm_ofEnergy, P.load_ofEnergy f hv hvp] at he
  · intro h v
    change intervalPeriodicPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      (P.boundary.ofEnergy hu hup.symm) v = P.load f v
    rw [intervalPeriodicPointForm_apply, P.load_representative]
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le
      P.site_mem (P.boundary.ofEnergy_representative hu hup.symm) (fun _ _ => rfl)]
    exact h (v.val.representative P.boundary.interval_pos)
      (v.val.representative_spec P.boundary.interval_pos).1
      (P.boundary.representative_periodic v).symm

theorem SignedPeriodicPointProblem.operator_graph_iff_physical (P : SignedPeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hup : u l = u r) :
    (P.boundary.stateL (P.boundary.ofEnergy hu hup.symm), f) ∈ P.operator.graph ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → v l = v r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ∫ x in l..r, f x * v x) := by
  rw [P.operator_graph_iff_state, P.weak_iff f hu hup]

theorem SignedPeriodicPointProblem.operator_graph_iff_exists_physical
    (P : SignedPeriodicPointProblem ι l r) (u f : IntervalSobolevL2 l r) :
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
