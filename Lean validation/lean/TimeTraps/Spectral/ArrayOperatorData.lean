module

public import TimeTraps.Analysis.IntervalPeriodicProblem
public import TimeTraps.Spectral.ArrayWeak

@[expose] public section

/-! Original arbitrary physical circle arrays as actual periodic operators.
The sites, strengths, physical interval and full H1 competitors are retained. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem PeriodicArray.operatorBoundary (P : PeriodicArray n) : IntervalPeriodicBoundary 0 P.length :=
  ⟨P.length_pos⟩

def PeriodicArray.periodicPointProblem (P : PeriodicArray n) :
    PeriodicPointProblem (Fin n) 0 P.length where
  boundary := P.operatorBoundary
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := P.strength
  strength_nonneg := fun i => (P.strength_pos i).le
  site := P.site
  site_mem := fun i => ⟨(P.site_mem i).1, (P.site_mem i).2.le⟩
  positive_contact := ⟨P.first, P.strength_pos P.first⟩

theorem PeriodicArray.operator_energy (P : PeriodicArray n)
    (u : IntervalPeriodicSpace P.operatorBoundary) :
    P.Energy (u.val.representative P.length_pos) :=
  ⟨(u.val.representative_spec P.length_pos).1, (P.operatorBoundary.representative_periodic u).symm⟩

noncomputable def PeriodicArray.operatorOfEnergy (P : PeriodicArray n)
    {u : ℝ → ℝ} (hu : P.Energy u) : IntervalPeriodicSpace P.operatorBoundary :=
  P.operatorBoundary.ofEnergy hu.1 hu.2.symm

theorem PeriodicArray.operatorOfEnergy_representative (P : PeriodicArray n)
    {u : ℝ → ℝ} (hu : P.Energy u) :
    EqOn ((P.operatorOfEnergy hu).val.representative P.length_pos) u (Icc 0 P.length) :=
  P.operatorBoundary.ofEnergy_representative hu.1 hu.2.symm

theorem PeriodicArray.operator_squareMass (P : PeriodicArray n)
    (u : IntervalPeriodicSpace P.operatorBoundary) :
    P.squareMass (u.val.representative P.length_pos) = ‖P.operatorBoundary.stateL u‖ ^ 2 := by
  change (∫ x in (0 : ℝ)..P.length, u.val.representative P.length_pos x ^ 2) = ‖u.val.state‖ ^ 2
  rw [← real_inner_self_eq_norm_sq, state_inner _ _ P.length_pos]
  simp only [pow_two]

end TimeTraps.Spectral
