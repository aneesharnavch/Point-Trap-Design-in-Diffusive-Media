module

public import TimeTraps.Spectral.RobinDirichletProblem
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-!
Convergence of the actual finite-Robin roots, not merely of a phase at fixed
wavenumber. Endpoint families may diverge at different rates. Root convergence
is proved from a uniform upper bound and eventual lower crossings, and then
the endpoint angles are evaluated along those moving roots.
-/

namespace TimeTraps.Spectral

open Set Filter
open scoped Topology BigOperators

variable {n : ℕ} {C : RobinPlacementProblem n} {α : Type*}

structure RobinDirichletFamily.EndpointLimit (F : RobinDirichletFamily C α)
    (left right : Bool) (l : Filter α) : Prop where
  left_fixed : left = false → ∀ t, F.leftCoefficient t = C.betaLeft
  right_fixed : right = false → ∀ t, F.rightCoefficient t = C.betaRight
  left_infinite : left = true → Tendsto F.leftCoefficient l atTop
  right_infinite : right = true → Tendsto F.rightCoefficient l atTop

theorem dirichlet_arctan_ratio_tendsto {l : Filter α} {b d : α → ℝ} {r : ℝ}
    (hr : 0 < r) (hb : Tendsto b l atTop) (hd : Tendsto d l (𝓝 r)) :
    Tendsto (fun t => Real.arctan (b t / d t)) l (𝓝 (Real.pi / 2)) := by
  have h := hb.atTop_mul_pos (inv_pos.mpr hr) (hd.inv₀ (ne_of_gt hr))
  have hdiv : Tendsto (fun t => b t / d t) l atTop := by simpa only [div_eq_mul_inv] using h
  exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hdiv

variable {F : RobinDirichletFamily C α} {left right : Bool} {l : Filter α}

theorem RobinDirichletFamily.capacity_tendsto (F : RobinDirichletFamily C α) (H : F.EndpointLimit left right l)
    {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t => F.capacity t k) l (𝓝 (C.dirichletCapacity left right k)) := by
  have h0 : Tendsto (fun t => Real.arctan ((F.leftCoefficient t / C.diffusivity) / k)) l
      (𝓝 (dirichletEndpointPhase (C.betaLeft / C.diffusivity) left k)) := by
    cases left
    · have he : (fun t => Real.arctan ((F.leftCoefficient t / C.diffusivity) / k)) =
          fun _ => Real.arctan ((C.betaLeft / C.diffusivity) / k) :=
        funext (fun t => by rw [H.left_fixed rfl t])
      rw [he]
      exact tendsto_const_nhds
    · simpa only [dirichletEndpointPhase, div_div, ↓reduceIte] using
        dirichlet_arctan_ratio_tendsto (mul_pos C.diffusivity_pos hk)
          (H.left_infinite rfl) (tendsto_const_nhds : Tendsto (fun _ : α => C.diffusivity * k) l _)
  have hL : Tendsto (fun t => Real.arctan ((F.rightCoefficient t / C.diffusivity) / k)) l
      (𝓝 (dirichletEndpointPhase (C.betaRight / C.diffusivity) right k)) := by
    cases right
    · have he : (fun t => Real.arctan ((F.rightCoefficient t / C.diffusivity) / k)) =
          fun _ => Real.arctan ((C.betaRight / C.diffusivity) / k) :=
        funext (fun t => by rw [H.right_fixed rfl t])
      rw [he]
      exact tendsto_const_nhds
    · simpa only [dirichletEndpointPhase, div_div, ↓reduceIte] using
        dirichlet_arctan_ratio_tendsto (mul_pos C.diffusivity_pos hk)
          (H.right_infinite rfl) (tendsto_const_nhds : Tendsto (fun _ : α => C.diffusivity * k) l _)
  exact (h0.add hL).add tendsto_const_nhds

theorem RobinDirichletFamily.root_tendsto (F : RobinDirichletFamily C α) (H : F.EndpointLimit left right l) :
    Tendsto (fun t => (F.problem t).root) l (𝓝 (C.dirichletRoot left right)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hapos : 0 < a
    · have hc := C.dirichletCapacity_strictAntiOn left right hapos
        (C.dirichletRoot_pos left right) ha
      have hlength := mul_lt_mul_of_pos_left ha C.length_pos
      have hstrict : C.length * a < C.dirichletCapacity left right a := by
        linarith [C.dirichletRoot_equation left right]
      filter_upwards [(F.capacity_tendsto H hapos).eventually (lt_mem_nhds hstrict)] with t ht
      exact F.lt_root_of_capacity t hapos ht
    · exact Eventually.of_forall (fun t => (le_of_not_gt hapos).trans_lt (F.problem t).root_pos)
  · intro b hb
    exact Eventually.of_forall (fun t =>
      (F.root_le_dirichlet left right H.left_fixed H.right_fixed t).trans_lt hb)

theorem RobinDirichletFamily.scaled_root_sq_tendsto (F : RobinDirichletFamily C α) (H : F.EndpointLimit left right l) :
    Tendsto (fun t => C.diffusivity * (F.problem t).root ^ 2) l
      (𝓝 (C.diffusivity * C.dirichletRoot left right ^ 2)) :=
  ((F.root_tendsto H).pow 2).const_mul C.diffusivity

theorem RobinDirichletFamily.leftAngle_tendsto (F : RobinDirichletFamily C α) (H : F.EndpointLimit left right l) :
    Tendsto (fun t => (F.problem t).leftAngle) l (𝓝 (C.dirichletLeftAngle left right)) := by
  have hroot := F.root_tendsto H
  have hden := hroot.const_mul C.diffusivity
  have hdenpos := mul_pos C.diffusivity_pos (C.dirichletRoot_pos left right)
  cases left
  · have hrat : Tendsto (fun t => C.betaLeft / (C.diffusivity * (F.problem t).root)) l
        (𝓝 (C.betaLeft / (C.diffusivity * C.dirichletRoot false right))) :=
      tendsto_const_nhds.div hden (ne_of_gt hdenpos)
    have ht := Real.continuous_arctan.continuousAt.tendsto.comp hrat
    have he : (fun t => (F.problem t).leftAngle) =
        fun t => Real.arctan (C.betaLeft / (C.diffusivity * (F.problem t).root)) := by
      funext t
      change Real.arctan (F.leftCoefficient t / (C.diffusivity * (F.problem t).root)) = _
      rw [H.left_fixed rfl t]
    rw [he]
    simpa [RobinPlacementProblem.dirichletLeftAngle, dirichletEndpointPhase, div_div,
      Function.comp_def] using ht
  · change Tendsto (fun t => Real.arctan (F.leftCoefficient t /
      (C.diffusivity * (F.problem t).root))) l (𝓝 (Real.pi / 2))
    exact dirichlet_arctan_ratio_tendsto hdenpos (H.left_infinite rfl) hden

theorem RobinDirichletFamily.rightAngle_tendsto (F : RobinDirichletFamily C α) (H : F.EndpointLimit left right l) :
    Tendsto (fun t => (F.problem t).rightAngle) l (𝓝 (C.dirichletRightAngle left right)) := by
  have hroot := F.root_tendsto H
  have hden := hroot.const_mul C.diffusivity
  have hdenpos := mul_pos C.diffusivity_pos (C.dirichletRoot_pos left right)
  cases right
  · have hrat : Tendsto (fun t => C.betaRight / (C.diffusivity * (F.problem t).root)) l
        (𝓝 (C.betaRight / (C.diffusivity * C.dirichletRoot left false))) :=
      tendsto_const_nhds.div hden (ne_of_gt hdenpos)
    have ht := Real.continuous_arctan.continuousAt.tendsto.comp hrat
    have he : (fun t => (F.problem t).rightAngle) =
        fun t => Real.arctan (C.betaRight / (C.diffusivity * (F.problem t).root)) := by
      funext t
      change Real.arctan (F.rightCoefficient t / (C.diffusivity * (F.problem t).root)) = _
      rw [H.right_fixed rfl t]
    rw [he]
    simpa [RobinPlacementProblem.dirichletRightAngle, dirichletEndpointPhase, div_div,
      Function.comp_def] using ht
  · change Tendsto (fun t => Real.arctan (F.rightCoefficient t /
      (C.diffusivity * (F.problem t).root))) l (𝓝 (Real.pi / 2))
    exact dirichlet_arctan_ratio_tendsto hdenpos (H.right_infinite rfl) hden

end TimeTraps.Spectral
