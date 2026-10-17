module

public import TimeTraps.Spectral.PhysicalProblem
public import TimeTraps.Spectral.RobinShooting
public import TimeTraps.Interval.HomogeneousMedium
public import TimeTraps.Interval.PiecewiseEnergy

@[expose] public section

/-!
Independent Robin spectral problem with nonnegative finite endpoint
coefficients. The full H1 Rayleigh form includes both endpoint reactions.
The principal value is defined before any shooting state is identified with it.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

structure RobinProblem (n : ℕ) extends SpectralProblem n where
  betaLeft : ℝ
  betaLeft_nonneg : 0 ≤ betaLeft
  betaRight : ℝ
  betaRight_nonneg : 0 ≤ betaRight

variable {n : ℕ}

def RobinProblem.geometry (P : RobinProblem n) : OrderedMedium n := P.toSpectralProblem.geometry

theorem RobinProblem.geometry_site (P : RobinProblem n) (i : Fin n) : P.geometry.site i = P.site i :=
  P.toSpectralProblem.geometry_site i

theorem RobinProblem.geometry_left (P : RobinProblem n) : P.geometry.source.left = 0 := rfl

theorem RobinProblem.geometry_right (P : RobinProblem n) : P.geometry.source.right = P.length := rfl

noncomputable def RobinProblem.shooting (P : RobinProblem n) : RobinShootingData n where
  gap := P.geometry.gapLength
  gap_pos := P.geometry.gapLength_pos
  reaction := fun i => P.strength i / P.diffusivity
  reaction_pos := fun i => div_pos (P.strength_pos i) P.diffusivity_pos
  leftRate := P.betaLeft / P.diffusivity
  leftRate_nonneg := div_nonneg P.betaLeft_nonneg P.diffusivity_pos.le
  rightRate := P.betaRight / P.diffusivity
  rightRate_nonneg := div_nonneg P.betaRight_nonneg P.diffusivity_pos.le

theorem RobinProblem.shooting_gap (P : RobinProblem n) (e : Fin (n + 1)) :
    P.shooting.gap e = P.geometry.node e.succ - P.geometry.node e.castSucc := rfl

theorem RobinProblem.shooting_reaction (P : RobinProblem n) (i : Fin n) :
    P.shooting.reaction i = P.strength i / P.diffusivity := rfl

theorem RobinProblem.shooting_leftRate (P : RobinProblem n) :
    P.shooting.leftRate = P.betaLeft / P.diffusivity := rfl

theorem RobinProblem.shooting_rightRate (P : RobinProblem n) :
    P.shooting.rightRate = P.betaRight / P.diffusivity := rfl

noncomputable def RobinProblem.quadraticForm (P : RobinProblem n) (v : ℝ → ℝ) : ℝ :=
  P.toSpectralProblem.quadraticForm v + P.betaLeft * v 0 ^ 2 + P.betaRight * v P.length ^ 2

noncomputable def RobinProblem.squareMass (P : RobinProblem n) (v : ℝ → ℝ) : ℝ :=
  P.toSpectralProblem.squareMass v

noncomputable def RobinProblem.reactionForm (P : RobinProblem n) (v : ℝ → ℝ) : ℝ :=
  (∑ i, P.strength i * v (P.site i) ^ 2) + P.betaLeft * v 0 ^ 2 + P.betaRight * v P.length ^ 2

theorem RobinProblem.quadraticForm_eq (P : RobinProblem n) (v : ℝ → ℝ) :
    P.quadraticForm v = P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv v x ^ 2) + P.reactionForm v := by
  unfold quadraticForm SpectralProblem.quadraticForm reactionForm
  ring

def RobinProblem.rayleighValues (P : RobinProblem n) : Set ℝ :=
  {r | ∃ v : ℝ → ℝ, IntervalEnergy v 0 P.length ∧ 0 < P.squareMass v ∧
    r = P.quadraticForm v / P.squareMass v}

/-- The principal variational value is defined before any shooting root is
identified with it. Its competitors are all nonzero physical H1 functions. -/
noncomputable def RobinProblem.principalValue (P : RobinProblem n) : ℝ := sInf P.rayleighValues

theorem RobinProblem.quadraticForm_nonneg (P : RobinProblem n) (v : ℝ → ℝ) :
    0 ≤ P.quadraticForm v :=
  add_nonneg (add_nonneg (P.toSpectralProblem.quadraticForm_nonneg v)
    (mul_nonneg P.betaLeft_nonneg (sq_nonneg _)))
    (mul_nonneg P.betaRight_nonneg (sq_nonneg _))

theorem RobinProblem.squareMass_one (P : RobinProblem n) : P.squareMass (fun _ => 1) = P.length := by
  exact P.toSpectralProblem.squareMass_one

theorem RobinProblem.rayleighValues_nonempty (P : RobinProblem n) : P.rayleighValues.Nonempty := by
  refine ⟨P.quadraticForm (fun _ => 1) / P.squareMass (fun _ => 1),
    (fun _ => 1), IntervalEnergy.const 1 0 P.length, ?_, rfl⟩
  rw [P.squareMass_one]
  exact P.length_pos

theorem RobinProblem.rayleighValues_bddBelow (P : RobinProblem n) : BddBelow P.rayleighValues := by
  refine ⟨0, ?_⟩
  rintro r ⟨v, _, hv, rfl⟩
  exact div_nonneg (P.quadraticForm_nonneg v) hv.le

theorem RobinProblem.principalValue_nonneg (P : RobinProblem n) : 0 ≤ P.principalValue := by
  apply le_csInf P.rayleighValues_nonempty
  rintro r ⟨v, _, hv, rfl⟩
  exact div_nonneg (P.quadraticForm_nonneg v) hv.le

end TimeTraps.Spectral
