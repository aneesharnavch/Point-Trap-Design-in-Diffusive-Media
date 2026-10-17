module

public import TimeTraps.Spectral.RobinDirichletSites
public import TimeTraps.Spectral.RobinPlacementNeumann

@[expose] public section

/-!
Consistency checks stated in the Robin source: retaining both finite
endpoints recovers the finite Robin root, empty interior phase sums give
the mixed and double-Dirichlet wavenumbers, and one Neumann interior trap
has its site at the midpoint and satisfies the equivalent tangent equation.
The empty-sum checks are scalar identities, not an extension of the
positive-interaction placement problem to zero interactions.
-/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval
open scoped BigOperators

variable {n : ℕ}

theorem RobinPlacementProblem.dirichletRoot_finite (C : RobinPlacementProblem n) :
    C.dirichletRoot false false = C.root := by
  apply C.eq_root (C.dirichletRoot_pos false false)
  simpa only [dirichletCapacity, dirichletPhaseCapacity, dirichletEndpointPhase,
    Bool.false_eq_true, if_false, phaseCapacity, div_div, Finset.mul_sum]
    using C.dirichletRoot_equation false false

theorem RobinPlacementProblem.dirichletRoot_neumann (C : RobinPlacementProblem n)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    C.dirichletRoot false false = C.toPlacementProblem.root :=
  C.dirichletRoot_finite.trans (C.root_neumann hleft hright)

theorem dirichlet_empty_mixed_root {L k : ℝ} (hL : 0 < L) :
    (L * k = dirichletPhaseCapacity (∅ : Finset Unit) (fun _ => 0) 0 0 false true k) ↔
      k = Real.pi / (2 * L) := by
  have hc : dirichletPhaseCapacity (∅ : Finset Unit) (fun _ => 0) 0 0 false true k =
      Real.pi / 2 := by simp [dirichletPhaseCapacity, dirichletEndpointPhase, phaseCapacity]
  rw [hc, eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hL))]
  constructor <;> intro h <;> nlinarith

theorem dirichlet_empty_double_root {L k : ℝ} (hL : 0 < L) :
    (L * k = dirichletPhaseCapacity (∅ : Finset Unit) (fun _ => 0) 0 0 true true k) ↔
      k = Real.pi / L := by
  have hc : dirichletPhaseCapacity (∅ : Finset Unit) (fun _ => 0) 0 0 true true k =
      Real.pi := by simp [dirichletPhaseCapacity, dirichletEndpointPhase, phaseCapacity]
  rw [hc, eq_div_iff (ne_of_gt hL)]
  constructor <;> intro h <;> nlinarith

theorem RobinPlacementProblem.one_trap_neumann_phase (C : RobinPlacementProblem 1)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    C.length * C.root = 2 * Real.arctan (C.strength 0 / (2 * C.diffusivity * C.root)) := by
  have h := C.toPlacementProblem.root_equation
  rw [← C.root_neumann hleft hright] at h
  simpa only [Fin.sum_univ_one] using h

theorem RobinPlacementProblem.one_trap_neumann_site (C : RobinPlacementProblem 1)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) : C.candidateSite 0 = C.length / 2 := by
  rw [C.candidateSite_neumann hleft hright]
  have hc : C.toPlacementProblem.cellLength 0 = C.length := by
    simpa only [Fin.sum_univ_one] using C.toPlacementProblem.cellLength_sum
  change C.toPlacementProblem.boundary 0 + C.toPlacementProblem.cellLength 0 / 2 = _
  rw [C.toPlacementProblem.boundary_zero, hc, zero_add]

theorem RobinPlacementProblem.one_trap_neumann_tangent (C : RobinPlacementProblem 1)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    2 * C.diffusivity * C.root * Real.tan (C.root * C.length / 2) = C.strength 0 := by
  have hhalf : C.root * C.length / 2 =
      Real.arctan (C.strength 0 / (2 * C.diffusivity * C.root)) := by
    nlinarith [C.one_trap_neumann_phase hleft hright]
  rw [hhalf, Real.tan_arctan]
  exact mul_div_cancel₀ _ (ne_of_gt (mul_pos (mul_pos (by norm_num) C.diffusivity_pos) C.root_pos))

theorem RobinPlacementProblem.one_trap_neumann_range (C : RobinPlacementProblem 1)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    0 < C.root * C.length ∧ C.root * C.length < Real.pi := by
  refine ⟨mul_pos C.root_pos C.length_pos, ?_⟩
  have he := C.one_trap_neumann_phase hleft hright
  have ha := Real.arctan_lt_pi_div_two (C.strength 0 / (2 * C.diffusivity * C.root))
  nlinarith

theorem RobinPlacementProblem.one_trap_neumann_tangent_iff (C : RobinPlacementProblem 1)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) {k : ℝ}
    (hk : 0 < k) (hkl : k * C.length < Real.pi) :
    (2 * C.diffusivity * k * Real.tan (k * C.length / 2) = C.strength 0) ↔ k = C.root := by
  constructor
  · intro he
    have hden : 0 < 2 * C.diffusivity * k :=
      mul_pos (mul_pos (by norm_num) C.diffusivity_pos) hk
    have ht : Real.tan (k * C.length / 2) = C.strength 0 / (2 * C.diffusivity * k) :=
      (eq_div_iff (ne_of_gt hden)).mpr (by nlinarith [he])
    have hlo : -(Real.pi / 2) < k * C.length / 2 := by
      nlinarith [mul_pos hk C.length_pos, Real.pi_pos]
    have hhi : k * C.length / 2 < Real.pi / 2 := by linarith
    have ha := congrArg Real.arctan ht
    rw [Real.arctan_tan hlo hhi] at ha
    apply C.eq_root hk
    simp only [hleft, hright, zero_div, Real.arctan_zero, zero_add, Fin.sum_univ_one]
    nlinarith
  · rintro rfl
    exact C.one_trap_neumann_tangent hleft hright

end TimeTraps.Spectral
