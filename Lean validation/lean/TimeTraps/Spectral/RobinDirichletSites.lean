module

public import TimeTraps.Spectral.RobinDirichletLimits

@[expose] public section

/-!
Every finite-Robin candidate site converges to its explicit Dirichlet-limit
formula. Both the endpoint phase and every interior phase are evaluated at
the moving root, whose convergence has already been proved.
-/

namespace TimeTraps.Spectral

open Set Filter TimeTraps.Interval
open scoped Topology BigOperators

variable {n : ℕ} {C : RobinPlacementProblem n} {α : Type*}
variable {left right : Bool} {l : Filter α}

theorem RobinDirichletFamily.angle_tendsto (F : RobinDirichletFamily C α)
    (H : F.EndpointLimit left right l) (i : Fin n) :
    Tendsto (fun t => (F.problem t).angle i) l (𝓝 (C.dirichletAngle left right i)) := by
  have hden := (F.root_tendsto H).const_mul (2 * C.diffusivity)
  have hdenpos := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) C.diffusivity_pos)
    (C.dirichletRoot_pos left right)
  have hrat : Tendsto (fun t => C.strength i / (2 * C.diffusivity * (F.problem t).root)) l
      (𝓝 (C.strength i / (2 * C.diffusivity * C.dirichletRoot left right))) :=
    tendsto_const_nhds.div hden (ne_of_gt hdenpos)
  exact Real.continuous_arctan.continuousAt.tendsto.comp hrat

theorem RobinDirichletFamily.prefix_tendsto (F : RobinDirichletFamily C α)
    (H : F.EndpointLimit left right l) (e : Fin (n + 1)) :
    Tendsto (fun t => absorptionPrefix (F.problem t).angle e) l
      (𝓝 (absorptionPrefix (C.dirichletAngle left right) e)) := by
  unfold absorptionPrefix
  apply tendsto_finsetSum
  intro i _
  by_cases hi : i.val < e.val
  · simpa only [if_pos hi] using F.angle_tendsto H i
  · simp only [if_neg hi]
    exact tendsto_const_nhds

theorem RobinDirichletFamily.candidateSite_tendsto (F : RobinDirichletFamily C α)
    (H : F.EndpointLimit left right l) (i : Fin n) :
    Tendsto (fun t => (F.problem t).candidateSite i) l (𝓝 (C.dirichletSite left right i)) := by
  have hnum := ((F.leftAngle_tendsto H).add ((F.prefix_tendsto H i.castSucc).const_mul 2)).add
    (F.angle_tendsto H i)
  have hquot := hnum.div (F.root_tendsto H) (ne_of_gt (C.dirichletRoot_pos left right))
  have he : (fun t => (F.problem t).candidateSite i) = fun t =>
      ((F.problem t).leftAngle + 2 * absorptionPrefix (F.problem t).angle i.castSucc +
        (F.problem t).angle i) / (F.problem t).root :=
    funext (fun t => (F.problem t).candidateSite_formula i)
  rw [he]
  exact hquot

end TimeTraps.Spectral
