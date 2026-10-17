module

public import TimeTraps.Spectral.ArrayOperatorGround

@[expose] public section

/-! The original circle cut at its first trap has the same actual periodic
operator, full physical weak equation and first eigenvalue as its independent
single-interval and intrinsic network Rayleigh problems. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

noncomputable def CircleProblem.operatorArray (C : CircleProblem n) : PeriodicArray n where
  count_pos := C.count_pos
  length := C.length
  length_pos := C.length_pos
  diffusivity := C.diffusivity
  diffusivity_pos := C.diffusivity_pos
  site := C.site
  site_strictMono := C.site_strictMono
  site_mem := C.site_mem
  strength := C.strength
  strength_pos := C.strength_pos

theorem CircleProblem.operatorArray_energy_iff (C : CircleProblem n) (u : ℝ → ℝ) :
    C.operatorArray.Energy u ↔ C.PeriodicEnergy u := Iff.rfl

theorem CircleProblem.operatorArray_rayleighValues (C : CircleProblem n) :
    C.operatorArray.rayleighValues = C.periodicRayleighValues := rfl

theorem CircleProblem.operatorArray_principalValue (C : CircleProblem n) :
    C.operatorArray.principalValue = C.periodicPrincipalValue := rfl

theorem CircleProblem.operatorArray_weak_iff (C : CircleProblem n) (ev : ℝ) (u : ℝ → ℝ) :
    ArrayWeakEigenEquation C.operatorArray ev u ↔ PeriodicWeakEigenEquation C ev u := by
  constructor
  · intro h
    exact ⟨h.energy, h.weak_form⟩
  · intro h
    exact ⟨h.energy, h.weak_form⟩

theorem CircleProblem.operator_weak_iff (C : CircleProblem n)
    (u : IntervalPeriodicSpace C.operatorArray.operatorBoundary) (ev : ℝ) :
    (C.operatorArray.operatorBoundary.stateL u, ev • C.operatorArray.operatorBoundary.stateL u) ∈
      C.operatorArray.periodicPointProblem.operator.graph ↔
        PeriodicWeakEigenEquation C ev (u.val.representative C.length_pos) := by
  rw [C.operatorArray.operator_weak_iff]
  exact C.operatorArray_weak_iff _ _

theorem CircleProblem.operator_first_eigenvalue (C : CircleProblem n) :
    (C.operatorArray.periodicPointProblem.spectralEnumeration 0).1⁻¹ =
      C.periodicPrincipalValue :=
  C.operatorArray.operator_first_eigenvalue

theorem CircleProblem.operator_first_eq_network_principal (C : CircleProblem n) :
    (C.operatorArray.periodicPointProblem.spectralEnumeration 0).1⁻¹ =
      C.network.principalValue := by
  rw [C.operator_first_eigenvalue, C.periodicPrincipalValue_eq]

theorem CircleProblem.operator_first_eigenstate_weak (C : CircleProblem n) :
    PeriodicWeakEigenEquation C C.periodicPrincipalValue
      ((C.operatorArray.periodicPointProblem.eigenstate
        (C.operatorArray.periodicPointProblem.spectralEnumeration 0)).val.representative
          C.length_pos) :=
  (C.operatorArray_weak_iff _ _).mp C.operatorArray.operator_first_eigenstate_weak

end TimeTraps.Spectral
