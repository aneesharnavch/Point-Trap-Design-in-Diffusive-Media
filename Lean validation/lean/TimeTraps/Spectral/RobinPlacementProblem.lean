module

public import TimeTraps.Spectral.PlacementProblem
public import TimeTraps.Spectral.RobinProblem
public import TimeTraps.Spectral.RobinCapacity

@[expose] public section

/-!
Prescribed interior strengths, endpoint coefficients, length and diffusivity
are fixed before the Robin sites are chosen. The independent Robin scalar root
determines a candidate placement. This module proves its geometric
admissibility and does not assume or assert its physical optimality.
-/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval
open scoped BigOperators

structure RobinPlacementProblem (n : ℕ) extends PlacementProblem n where
  betaLeft : ℝ
  betaLeft_nonneg : 0 ≤ betaLeft
  betaRight : ℝ
  betaRight_nonneg : 0 ≤ betaRight

variable {n : ℕ}

def RobinPlacementProblem.Admissible (C : RobinPlacementProblem n) (x : Fin n → ℝ) : Prop :=
  C.toPlacementProblem.Admissible x

def RobinPlacementProblem.physical (C : RobinPlacementProblem n) (x : Fin n → ℝ)
    (hx : C.Admissible x) : RobinProblem n where
  toSpectralProblem := C.toPlacementProblem.physical x hx
  betaLeft := C.betaLeft
  betaLeft_nonneg := C.betaLeft_nonneg
  betaRight := C.betaRight
  betaRight_nonneg := C.betaRight_nonneg

theorem RobinPlacementProblem.root_existsUnique (C : RobinPlacementProblem n) :
    ∃! k : ℝ, 0 < k ∧ C.length * k =
      Real.arctan (C.betaLeft / (C.diffusivity * k)) +
      Real.arctan (C.betaRight / (C.diffusivity * k)) +
        2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k)) :=
  robin_spectral_root_existsUnique Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    C.strength (fun i _ => C.strength_pos i) C.diffusivity_pos C.length_pos
    C.betaLeft_nonneg C.betaRight_nonneg

noncomputable def RobinPlacementProblem.root (C : RobinPlacementProblem n) : ℝ :=
  Classical.choose C.root_existsUnique

theorem RobinPlacementProblem.root_pos (C : RobinPlacementProblem n) : 0 < C.root :=
  (Classical.choose_spec C.root_existsUnique).1.1

theorem RobinPlacementProblem.root_equation (C : RobinPlacementProblem n) :
    C.length * C.root =
      Real.arctan (C.betaLeft / (C.diffusivity * C.root)) +
      Real.arctan (C.betaRight / (C.diffusivity * C.root)) +
        2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * C.root)) :=
  (Classical.choose_spec C.root_existsUnique).1.2

theorem RobinPlacementProblem.eq_root (C : RobinPlacementProblem n) {k : ℝ} (hk : 0 < k)
    (he : C.length * k =
      Real.arctan (C.betaLeft / (C.diffusivity * k)) +
      Real.arctan (C.betaRight / (C.diffusivity * k)) +
        2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) : k = C.root :=
  (Classical.choose_spec C.root_existsUnique).2 k ⟨hk, he⟩

noncomputable def RobinPlacementProblem.angle (C : RobinPlacementProblem n) (i : Fin n) : ℝ :=
  Real.arctan (C.strength i / (2 * C.diffusivity * C.root))

noncomputable def RobinPlacementProblem.leftAngle (C : RobinPlacementProblem n) : ℝ :=
  Real.arctan (C.betaLeft / (C.diffusivity * C.root))

noncomputable def RobinPlacementProblem.rightAngle (C : RobinPlacementProblem n) : ℝ :=
  Real.arctan (C.betaRight / (C.diffusivity * C.root))

theorem RobinPlacementProblem.angle_pos (C : RobinPlacementProblem n) (i : Fin n) : 0 < C.angle i :=
  Real.arctan_pos.mpr (div_pos (C.strength_pos i)
    (mul_pos (mul_pos (by norm_num) C.diffusivity_pos) C.root_pos))

theorem RobinPlacementProblem.angle_lt (C : RobinPlacementProblem n) (i : Fin n) :
    C.angle i < Real.pi / 2 := Real.arctan_lt_pi_div_two _

theorem RobinPlacementProblem.leftAngle_nonneg (C : RobinPlacementProblem n) : 0 ≤ C.leftAngle :=
  Real.arctan_nonneg.mpr (div_nonneg C.betaLeft_nonneg (mul_pos C.diffusivity_pos C.root_pos).le)

theorem RobinPlacementProblem.rightAngle_nonneg (C : RobinPlacementProblem n) : 0 ≤ C.rightAngle :=
  Real.arctan_nonneg.mpr (div_nonneg C.betaRight_nonneg (mul_pos C.diffusivity_pos C.root_pos).le)

theorem RobinPlacementProblem.leftAngle_lt (C : RobinPlacementProblem n) :
    C.leftAngle < Real.pi / 2 := Real.arctan_lt_pi_div_two _

theorem RobinPlacementProblem.rightAngle_lt (C : RobinPlacementProblem n) :
    C.rightAngle < Real.pi / 2 := Real.arctan_lt_pi_div_two _

theorem RobinPlacementProblem.angle_equation (C : RobinPlacementProblem n) :
    C.length * C.root = C.leftAngle + C.rightAngle + 2 * ∑ i, C.angle i := C.root_equation

noncomputable def RobinPlacementProblem.cellLength (C : RobinPlacementProblem n) (i : Fin n) : ℝ :=
  2 * C.angle i / C.root

theorem RobinPlacementProblem.cellLength_pos (C : RobinPlacementProblem n) (i : Fin n) :
    0 < C.cellLength i := div_pos (mul_pos (by norm_num) (C.angle_pos i)) C.root_pos

noncomputable def RobinPlacementProblem.boundary (C : RobinPlacementProblem n) (e : Fin (n + 1)) : ℝ :=
  (C.leftAngle + 2 * absorptionPrefix C.angle e) / C.root

theorem RobinPlacementProblem.boundary_zero (C : RobinPlacementProblem n) :
    C.boundary 0 = C.leftAngle / C.root := by
  rw [boundary, absorptionPrefix_zero]
  ring

theorem RobinPlacementProblem.boundary_succ (C : RobinPlacementProblem n) (i : Fin n) :
    C.boundary i.succ = C.boundary i.castSucc + C.cellLength i := by
  unfold boundary cellLength
  rw [absorptionPrefix_succ]
  ring

theorem RobinPlacementProblem.boundary_last (C : RobinPlacementProblem n) :
    C.boundary (Fin.last n) = C.length - C.rightAngle / C.root := by
  rw [boundary, absorptionPrefix_last]
  apply (div_eq_iff (ne_of_gt C.root_pos)).mpr
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt C.root_pos)]
  linarith [C.angle_equation]

theorem RobinPlacementProblem.boundary_strictMono (C : RobinPlacementProblem n) :
    StrictMono C.boundary := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [C.boundary_succ]
  exact lt_add_of_pos_right _ (C.cellLength_pos i)

theorem RobinPlacementProblem.boundary_mem (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.boundary e ∈ Icc (0 : ℝ) C.length := by
  have hzero : 0 ≤ C.boundary 0 := by
    rw [C.boundary_zero]
    exact div_nonneg C.leftAngle_nonneg C.root_pos.le
  have hlast : C.boundary (Fin.last n) ≤ C.length := by
    rw [C.boundary_last]
    exact sub_le_self _ (div_nonneg C.rightAngle_nonneg C.root_pos.le)
  exact ⟨hzero.trans (C.boundary_strictMono.monotone (Fin.zero_le e)),
    (C.boundary_strictMono.monotone (Fin.le_last e)).trans hlast⟩

noncomputable def RobinPlacementProblem.candidateSite (C : RobinPlacementProblem n) (i : Fin n) : ℝ :=
  C.boundary i.castSucc + C.cellLength i / 2

theorem RobinPlacementProblem.candidateSite_formula (C : RobinPlacementProblem n) (i : Fin n) :
    C.candidateSite i =
      (C.leftAngle + 2 * absorptionPrefix C.angle i.castSucc + C.angle i) / C.root := by
  unfold candidateSite boundary cellLength
  ring

theorem RobinPlacementProblem.candidateSite_in_cell (C : RobinPlacementProblem n) (i : Fin n) :
    C.candidateSite i ∈ Ioo (C.boundary i.castSucc) (C.boundary i.succ) := by
  rw [candidateSite, C.boundary_succ]
  constructor <;> linarith [C.cellLength_pos i]

theorem RobinPlacementProblem.candidateSite_admissible (C : RobinPlacementProblem n) :
    C.Admissible C.candidateSite := by
  constructor
  · intro i j hij
    have hi : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
    exact ((C.candidateSite_in_cell i).2.trans_le (C.boundary_strictMono.monotone hi)).trans
      (C.candidateSite_in_cell j).1
  · intro i
    exact ⟨(C.boundary_mem i.castSucc).1.trans_lt (C.candidateSite_in_cell i).1,
      (C.candidateSite_in_cell i).2.trans_le (C.boundary_mem i.succ).2⟩

noncomputable def RobinPlacementProblem.candidatePhysical (C : RobinPlacementProblem n) : RobinProblem n :=
  C.physical C.candidateSite C.candidateSite_admissible

end TimeTraps.Spectral
