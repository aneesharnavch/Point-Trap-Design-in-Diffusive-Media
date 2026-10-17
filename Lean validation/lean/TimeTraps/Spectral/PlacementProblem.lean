module

public import TimeTraps.Spectral.PrincipalBound

@[expose] public section

/-!
Prescribed ordered strengths, length and diffusivity are fixed before the
sites are chosen. The scalar capacity root determines positive cell lengths
and their interior midpoints. Optimality is not built into admissibility.
-/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval
open scoped BigOperators

structure PlacementProblem (n : ℕ) where
  count_pos : 0 < n
  length : ℝ
  length_pos : 0 < length
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  strength : Fin n → ℝ
  strength_pos : ∀ i, 0 < strength i

variable {n : ℕ}

def PlacementProblem.Admissible (C : PlacementProblem n) (x : Fin n → ℝ) : Prop :=
  StrictMono x ∧ ∀ i, x i ∈ Ioo (0 : ℝ) C.length

def PlacementProblem.physical (C : PlacementProblem n) (x : Fin n → ℝ) (hx : C.Admissible x) :
    SpectralProblem n where
  count_pos := C.count_pos
  length := C.length
  length_pos := C.length_pos
  diffusivity := C.diffusivity
  diffusivity_pos := C.diffusivity_pos
  site := x
  site_strictMono := hx.1
  site_interior := hx.2
  strength := C.strength
  strength_pos := C.strength_pos

theorem PlacementProblem.root_existsUnique (C : PlacementProblem n) :
    ∃! k : ℝ, 0 < k ∧ C.length * k = 2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k)) :=
  spectral_root_existsUnique Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    C.strength (fun i _ => C.strength_pos i) C.diffusivity_pos C.length_pos

noncomputable def PlacementProblem.root (C : PlacementProblem n) : ℝ :=
  Classical.choose C.root_existsUnique

theorem PlacementProblem.root_pos (C : PlacementProblem n) : 0 < C.root :=
  (Classical.choose_spec C.root_existsUnique).1.1

theorem PlacementProblem.root_equation (C : PlacementProblem n) :
    C.length * C.root = 2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * C.root)) :=
  (Classical.choose_spec C.root_existsUnique).1.2

theorem PlacementProblem.eq_root (C : PlacementProblem n) {k : ℝ} (hk : 0 < k)
    (he : C.length * k = 2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) : k = C.root :=
  (Classical.choose_spec C.root_existsUnique).2 k ⟨hk, he⟩

noncomputable def PlacementProblem.angle (C : PlacementProblem n) (i : Fin n) : ℝ :=
  Real.arctan (C.strength i / (2 * C.diffusivity * C.root))

theorem PlacementProblem.angle_pos (C : PlacementProblem n) (i : Fin n) : 0 < C.angle i :=
  Real.arctan_pos.mpr (div_pos (C.strength_pos i)
    (mul_pos (mul_pos (by norm_num) C.diffusivity_pos) C.root_pos))

theorem PlacementProblem.angle_lt (C : PlacementProblem n) (i : Fin n) : C.angle i < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

noncomputable def PlacementProblem.cellLength (C : PlacementProblem n) (i : Fin n) : ℝ :=
  2 * C.angle i / C.root

theorem PlacementProblem.cellLength_pos (C : PlacementProblem n) (i : Fin n) : 0 < C.cellLength i :=
  div_pos (mul_pos (by norm_num) (C.angle_pos i)) C.root_pos

theorem PlacementProblem.cellLength_sum (C : PlacementProblem n) : (∑ i, C.cellLength i) = C.length := by
  unfold cellLength
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change (2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * C.root))) / C.root = C.length
  rw [← C.root_equation, mul_div_cancel_right₀ _ (ne_of_gt C.root_pos)]

noncomputable def PlacementProblem.boundary (C : PlacementProblem n) : Fin (n + 1) → ℝ :=
  absorptionPrefix C.cellLength

theorem PlacementProblem.boundary_zero (C : PlacementProblem n) : C.boundary 0 = 0 :=
  absorptionPrefix_zero _

theorem PlacementProblem.boundary_succ (C : PlacementProblem n) (i : Fin n) :
    C.boundary i.succ = C.boundary i.castSucc + C.cellLength i := absorptionPrefix_succ _ i

theorem PlacementProblem.boundary_last (C : PlacementProblem n) : C.boundary (Fin.last n) = C.length := by
  rw [boundary, absorptionPrefix_last, C.cellLength_sum]

theorem PlacementProblem.boundary_strictMono (C : PlacementProblem n) : StrictMono C.boundary := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [C.boundary_succ]
  exact lt_add_of_pos_right _ (C.cellLength_pos i)

theorem PlacementProblem.boundary_mem (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.boundary e ∈ Icc (0 : ℝ) C.length := by
  rw [← C.boundary_zero, ← C.boundary_last]
  exact ⟨C.boundary_strictMono.monotone (Fin.zero_le e), C.boundary_strictMono.monotone (Fin.le_last e)⟩

noncomputable def PlacementProblem.optimalSite (C : PlacementProblem n) (i : Fin n) : ℝ :=
  C.boundary i.castSucc + C.cellLength i / 2

theorem PlacementProblem.optimalSite_in_cell (C : PlacementProblem n) (i : Fin n) :
    C.optimalSite i ∈ Ioo (C.boundary i.castSucc) (C.boundary i.succ) := by
  rw [optimalSite, C.boundary_succ]
  constructor <;> linarith [C.cellLength_pos i]

theorem PlacementProblem.optimalSite_admissible (C : PlacementProblem n) : C.Admissible C.optimalSite := by
  constructor
  · intro i j hij
    have hi : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
    exact ((C.optimalSite_in_cell i).2.trans_le (C.boundary_strictMono.monotone hi)).trans
      (C.optimalSite_in_cell j).1
  · intro i
    exact ⟨(C.boundary_mem i.castSucc).1.trans_lt (C.optimalSite_in_cell i).1,
      (C.optimalSite_in_cell i).2.trans_le (C.boundary_mem i.succ).2⟩

noncomputable def PlacementProblem.optimalPhysical (C : PlacementProblem n) : SpectralProblem n :=
  C.physical C.optimalSite C.optimalSite_admissible

theorem PlacementProblem.arbitrary_upper_bound (C : PlacementProblem n) (x : Fin n → ℝ)
    (hx : C.Admissible x) : (C.physical x hx).principalValue ≤ C.diffusivity * C.root ^ 2 :=
  (C.physical x hx).principalValue_le_root C.root_pos C.root_equation

end TimeTraps.Spectral
