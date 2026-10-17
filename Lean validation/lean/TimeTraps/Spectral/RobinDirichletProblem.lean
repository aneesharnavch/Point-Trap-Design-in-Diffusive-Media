module

public import TimeTraps.Spectral.RobinDirichletCapacity
public import TimeTraps.Spectral.RobinPlacementProblem

@[expose] public section

/-!
The limiting root and explicit limiting sites for fixed physical interior
data. A Robin coefficient family contains only nonnegative coefficients;
its roots are the actual independently defined finite-Robin roots. Their
monotonicity and comparison with the limiting root are proved here.
-/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval
open scoped BigOperators

variable {n : ℕ}

noncomputable def RobinPlacementProblem.dirichletCapacity (C : RobinPlacementProblem n)
    (left right : Bool) (k : ℝ) : ℝ :=
  dirichletPhaseCapacity Finset.univ (fun i => C.strength i / (2 * C.diffusivity))
    (C.betaLeft / C.diffusivity) (C.betaRight / C.diffusivity) left right k

theorem RobinPlacementProblem.dirichletRoot_existsUnique (C : RobinPlacementProblem n)
    (left right : Bool) : ∃! k : ℝ, 0 < k ∧ C.length * k = C.dirichletCapacity left right k :=
  dirichlet_capacity_root_existsUnique Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    (div_nonneg C.betaLeft_nonneg C.diffusivity_pos.le)
    (div_nonneg C.betaRight_nonneg C.diffusivity_pos.le) left right C.length_pos

noncomputable def RobinPlacementProblem.dirichletRoot (C : RobinPlacementProblem n)
    (left right : Bool) : ℝ := Classical.choose (C.dirichletRoot_existsUnique left right)

theorem RobinPlacementProblem.dirichletRoot_pos (C : RobinPlacementProblem n) (left right : Bool) :
    0 < C.dirichletRoot left right := (Classical.choose_spec (C.dirichletRoot_existsUnique left right)).1.1

theorem RobinPlacementProblem.dirichletRoot_equation (C : RobinPlacementProblem n) (left right : Bool) :
    C.length * C.dirichletRoot left right = C.dirichletCapacity left right (C.dirichletRoot left right) :=
  (Classical.choose_spec (C.dirichletRoot_existsUnique left right)).1.2

theorem RobinPlacementProblem.dirichletCapacity_strictAntiOn (C : RobinPlacementProblem n)
    (left right : Bool) : StrictAntiOn (C.dirichletCapacity left right) (Ioi 0) :=
  dirichletPhaseCapacity_strictAntiOn Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    (div_nonneg C.betaLeft_nonneg C.diffusivity_pos.le)
    (div_nonneg C.betaRight_nonneg C.diffusivity_pos.le) left right

theorem RobinPlacementProblem.le_dirichletRoot (C : RobinPlacementProblem n)
    (left right : Bool) {k : ℝ} (hk : 0 < k)
    (hbound : C.length * k ≤ C.dirichletCapacity left right k) : k ≤ C.dirichletRoot left right :=
  le_dirichlet_capacity_root Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    (div_nonneg C.betaLeft_nonneg C.diffusivity_pos.le)
    (div_nonneg C.betaRight_nonneg C.diffusivity_pos.le) left right C.length_pos hk
    (C.dirichletRoot_pos left right) (C.dirichletRoot_equation left right) hbound

theorem RobinPlacementProblem.dirichletRoot_upper (C : RobinPlacementProblem n) (left right : Bool) :
    C.dirichletRoot left right ≤ ((n : ℝ) + 1) * Real.pi / C.length := by
  have h := dirichletPhaseCapacity_le_bound Finset.univ
    (fun i => C.strength i / (2 * C.diffusivity)) (C.betaLeft / C.diffusivity)
    (C.betaRight / C.diffusivity) left right (C.dirichletRoot left right)
  change C.dirichletCapacity left right (C.dirichletRoot left right) ≤ _ at h
  rw [← C.dirichletRoot_equation] at h
  apply (le_div_iff₀ C.length_pos).mpr
  simpa only [Finset.card_univ, Fintype.card_fin, mul_comm] using h

noncomputable def RobinPlacementProblem.dirichletAngle (C : RobinPlacementProblem n)
    (left right : Bool) (i : Fin n) : ℝ :=
  Real.arctan (C.strength i / (2 * C.diffusivity * C.dirichletRoot left right))

noncomputable def RobinPlacementProblem.dirichletLeftAngle (C : RobinPlacementProblem n)
    (left right : Bool) : ℝ :=
  dirichletEndpointPhase (C.betaLeft / C.diffusivity) left (C.dirichletRoot left right)

noncomputable def RobinPlacementProblem.dirichletRightAngle (C : RobinPlacementProblem n)
    (left right : Bool) : ℝ :=
  dirichletEndpointPhase (C.betaRight / C.diffusivity) right (C.dirichletRoot left right)

noncomputable def RobinPlacementProblem.dirichletSite (C : RobinPlacementProblem n)
    (left right : Bool) (i : Fin n) : ℝ :=
  (C.dirichletLeftAngle left right + 2 * absorptionPrefix (C.dirichletAngle left right) i.castSucc +
    C.dirichletAngle left right i) / C.dirichletRoot left right

structure RobinDirichletFamily (C : RobinPlacementProblem n) (α : Type*) where
  leftCoefficient : α → ℝ
  rightCoefficient : α → ℝ
  left_nonneg : ∀ t, 0 ≤ leftCoefficient t
  right_nonneg : ∀ t, 0 ≤ rightCoefficient t

variable {C : RobinPlacementProblem n} {α : Type*}

def RobinDirichletFamily.problem (F : RobinDirichletFamily C α) (t : α) : RobinPlacementProblem n where
  toPlacementProblem := C.toPlacementProblem
  betaLeft := F.leftCoefficient t
  betaLeft_nonneg := F.left_nonneg t
  betaRight := F.rightCoefficient t
  betaRight_nonneg := F.right_nonneg t

noncomputable def RobinDirichletFamily.capacity (F : RobinDirichletFamily C α) (t : α) (k : ℝ) : ℝ :=
  robinPhaseCapacity Finset.univ (fun i => C.strength i / (2 * C.diffusivity))
    (F.leftCoefficient t / C.diffusivity) (F.rightCoefficient t / C.diffusivity) k

theorem RobinDirichletFamily.root_equation (F : RobinDirichletFamily C α) (t : α) :
    C.length * (F.problem t).root = F.capacity t (F.problem t).root := by
  simpa only [capacity, robinPhaseCapacity, phaseCapacity, div_div, Finset.mul_sum, problem]
    using (F.problem t).root_equation

theorem RobinDirichletFamily.le_root_of_capacity (F : RobinDirichletFamily C α) (t : α)
    {k : ℝ} (hk : 0 < k) (hbound : C.length * k ≤ F.capacity t k) : k ≤ (F.problem t).root :=
  le_robin_capacity_root Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    (div_nonneg (F.left_nonneg t) C.diffusivity_pos.le)
    (div_nonneg (F.right_nonneg t) C.diffusivity_pos.le) C.length_pos hk
    (F.problem t).root_pos (F.root_equation t) hbound

theorem RobinDirichletFamily.lt_root_of_capacity (F : RobinDirichletFamily C α) (t : α)
    {k : ℝ} (hk : 0 < k) (hbound : C.length * k < F.capacity t k) : k < (F.problem t).root :=
  lt_robin_capacity_root Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    (div_nonneg (F.left_nonneg t) C.diffusivity_pos.le)
    (div_nonneg (F.right_nonneg t) C.diffusivity_pos.le) C.length_pos hk
    (F.problem t).root_pos (F.root_equation t) hbound

theorem RobinDirichletFamily.capacity_mono_coefficients (F : RobinDirichletFamily C α)
    {s t : α} (h0 : F.leftCoefficient s ≤ F.leftCoefficient t)
    (hL : F.rightCoefficient s ≤ F.rightCoefficient t) {k : ℝ} (hk : 0 < k) :
    F.capacity s k ≤ F.capacity t k := by
  have h0' := Real.arctan_strictMono.monotone
    (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h0 C.diffusivity_pos.le) hk.le)
  have hL' := Real.arctan_strictMono.monotone
    (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hL C.diffusivity_pos.le) hk.le)
  unfold capacity robinPhaseCapacity
  linarith

theorem RobinDirichletFamily.root_le_of_coefficients (F : RobinDirichletFamily C α)
    {s t : α} (h0 : F.leftCoefficient s ≤ F.leftCoefficient t)
    (hL : F.rightCoefficient s ≤ F.rightCoefficient t) : (F.problem s).root ≤ (F.problem t).root := by
  apply F.le_root_of_capacity t (F.problem s).root_pos
  rw [F.root_equation]
  exact F.capacity_mono_coefficients h0 hL (F.problem s).root_pos

theorem RobinDirichletFamily.root_monotone [Preorder α] (F : RobinDirichletFamily C α)
    (h0 : Monotone F.leftCoefficient) (hL : Monotone F.rightCoefficient) :
    Monotone (fun t => (F.problem t).root) :=
  fun _ _ hst => F.root_le_of_coefficients (h0 hst) (hL hst)

theorem RobinDirichletFamily.capacity_le_dirichlet (F : RobinDirichletFamily C α)
    (left right : Bool)
    (h0 : left = false → ∀ t, F.leftCoefficient t = C.betaLeft)
    (hL : right = false → ∀ t, F.rightCoefficient t = C.betaRight) (t : α) (k : ℝ) :
    F.capacity t k ≤ C.dirichletCapacity left right k := by
  have hl : Real.arctan ((F.leftCoefficient t / C.diffusivity) / k) ≤
      dirichletEndpointPhase (C.betaLeft / C.diffusivity) left k := by
    cases left
    · rw [h0 rfl t]
      exact le_rfl
    · exact (Real.arctan_lt_pi_div_two _).le
  have hr : Real.arctan ((F.rightCoefficient t / C.diffusivity) / k) ≤
      dirichletEndpointPhase (C.betaRight / C.diffusivity) right k := by
    cases right
    · rw [hL rfl t]
      exact le_rfl
    · exact (Real.arctan_lt_pi_div_two _).le
  unfold capacity robinPhaseCapacity RobinPlacementProblem.dirichletCapacity dirichletPhaseCapacity
  linarith

theorem RobinDirichletFamily.root_le_dirichlet (F : RobinDirichletFamily C α)
    (left right : Bool)
    (h0 : left = false → ∀ t, F.leftCoefficient t = C.betaLeft)
    (hL : right = false → ∀ t, F.rightCoefficient t = C.betaRight) (t : α) :
    (F.problem t).root ≤ C.dirichletRoot left right := by
  apply C.le_dirichletRoot left right (F.problem t).root_pos
  rw [F.root_equation]
  exact F.capacity_le_dirichlet left right h0 hL t _

end TimeTraps.Spectral
