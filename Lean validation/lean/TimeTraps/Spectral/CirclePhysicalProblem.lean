module

public import TimeTraps.Spectral.CircleCut

@[expose] public section

/-! Independent single-interval periodic H1 class and Rayleigh quotient.
The trap at the cut is included once in the reaction sum. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

def CircleProblem.PeriodicEnergy (C : CircleProblem n) (w : ℝ → ℝ) : Prop :=
  IntervalEnergy w 0 C.length ∧ w 0 = w C.length

noncomputable def CircleProblem.periodicQuadraticForm (C : CircleProblem n) (w : ℝ → ℝ) : ℝ :=
  C.diffusivity * (∫ x in (0 : ℝ)..C.length, deriv w x ^ 2) +
    ∑ i, C.strength i * w (C.site i) ^ 2

noncomputable def CircleProblem.periodicMass (C : CircleProblem n) (w : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..C.length, w x ^ 2

def CircleProblem.periodicRayleighValues (C : CircleProblem n) : Set ℝ :=
  {r | ∃ w : ℝ → ℝ, C.PeriodicEnergy w ∧ 0 < C.periodicMass w ∧
    r = C.periodicQuadraticForm w / C.periodicMass w}

noncomputable def CircleProblem.periodicPrincipalValue (C : CircleProblem n) : ℝ :=
  sInf C.periodicRayleighValues

noncomputable def CircleProblem.restriction (C : CircleProblem n) (w : ℝ → ℝ)
    (i : Fin n) (x : ℝ) : ℝ := w (C.site i + x)

theorem CircleProblem.periodicEnergy_const (C : CircleProblem n) (c : ℝ) :
    C.PeriodicEnergy (fun _ => c) := ⟨IntervalEnergy.const c 0 C.length, rfl⟩

theorem CircleProblem.periodicMass_one (C : CircleProblem n) : C.periodicMass (fun _ => 1) = C.length := by
  simp [periodicMass]

theorem CircleProblem.periodicRayleighValues_nonempty (C : CircleProblem n) :
    C.periodicRayleighValues.Nonempty := by
  refine ⟨C.periodicQuadraticForm (fun _ => 1) / C.periodicMass (fun _ => 1),
    (fun _ => 1), C.periodicEnergy_const 1, ?_, rfl⟩
  rw [C.periodicMass_one]
  exact C.length_pos

theorem CircleProblem.periodic_cut_nodes (C : CircleProblem (n + 1)) {w : ℝ → ℝ}
    (hw : w 0 = w C.length) :
    (fun v => w (C.cut.node v)) = circleCutNodes (fun i => w (C.site i)) := by
  funext v
  refine Fin.lastCases ?_ (fun e => ?_) v
  · rw [C.cut.node_last, circleCutNodes_last]
    have hsite : C.site (0 : Fin (n + 1)) = 0 := C.site_zero
    rw [hsite]
    exact hw.symm
  · rw [circleCutNodes_castSucc]
    rfl

theorem CircleProblem.restrict_periodic_energy (C : CircleProblem n) {w : ℝ → ℝ}
    (hw : C.PeriodicEnergy w) : GraphEnergy C.network.geometry (fun i => w (C.site i)) (C.restriction w) := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    have h := C.cut.restrict_energy hw.1
    rw [C.periodic_cut_nodes hw.2] at h
    exact C.from_cut_energy h

theorem CircleProblem.restriction_deriv (C : CircleProblem n) (w : ℝ → ℝ) (i : Fin n) (x : ℝ) :
    deriv (C.restriction w i) x = deriv w (C.site i + x) :=
  deriv_comp_const_add w (C.site i) x

theorem CircleProblem.restrict_mass (C : CircleProblem n) {w : ℝ → ℝ}
    (hw : IntervalEnergy w 0 C.length) : C.network.squareMass (C.restriction w) = C.periodicMass w := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    have h := C.cut.integral_gap_sum hw.state_square_integrable
    simp_rw [C.cut_gapLength] at h
    exact h

theorem CircleProblem.restrict_derivative_energy (C : CircleProblem n) {w : ℝ → ℝ}
    (hw : IntervalEnergy w 0 C.length) :
    (∑ i, ∫ x in (0 : ℝ)..C.gap i, deriv (C.restriction w i) x ^ 2) =
      ∫ x in (0 : ℝ)..C.length, deriv w x ^ 2 := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    simp_rw [C.restriction_deriv]
    have h := C.cut.integral_gap_sum hw.derivative_square_integrable
    simp_rw [C.cut_gapLength] at h
    exact h

theorem CircleProblem.restrict_quadraticForm (C : CircleProblem n) {w : ℝ → ℝ}
    (hw : IntervalEnergy w 0 C.length) :
    C.network.quadraticForm (fun i => w (C.site i)) (C.restriction w) = C.periodicQuadraticForm w := by
  change C.diffusivity * (∑ i, ∫ x in (0 : ℝ)..C.gap i, deriv (C.restriction w i) x ^ 2) +
    (∑ i, C.strength i * w (C.site i) ^ 2) = _
  rw [C.restrict_derivative_energy hw]
  rfl

end TimeTraps.Spectral
