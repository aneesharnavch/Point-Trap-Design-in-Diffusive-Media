module

public import TimeTraps.Analysis.IntervalCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! A strictly increasing unit-interval coordinate with both first and
second derivatives zero at the endpoints. This endpoint flatness will
make graph coordinate fluxes and their generators match at vertices. -/

namespace TimeTraps.Analysis

open Set

def graphSmoothStep (s : ℝ) : ℝ := 10 * s ^ 3 - 15 * s ^ 4 + 6 * s ^ 5

def graphSmoothStepSlope (s : ℝ) : ℝ := 30 * s ^ 2 * (1 - s) ^ 2

def graphSmoothStepCurvature (s : ℝ) : ℝ := 60 * s * (1 - s) * (1 - 2 * s)

theorem graphSmoothStep_hasDerivAt (s : ℝ) :
    HasDerivAt graphSmoothStep (graphSmoothStepSlope s) s := by
  convert! ((((hasDerivAt_id s).pow 3).const_mul 10).sub
    (((hasDerivAt_id s).pow 4).const_mul 15)).add
      (((hasDerivAt_id s).pow 5).const_mul 6) using 1
  dsimp [graphSmoothStepSlope]
  ring

theorem graphSmoothStepSlope_hasDerivAt (s : ℝ) :
    HasDerivAt graphSmoothStepSlope (graphSmoothStepCurvature s) s := by
  convert! (((hasDerivAt_id s).pow 2).const_mul 30).mul
    (((hasDerivAt_const s 1).sub (hasDerivAt_id s)).pow 2) using 1
  dsimp [graphSmoothStepCurvature]
  ring

theorem graphSmoothStep_endpoints :
    graphSmoothStep 0 = 0 ∧ graphSmoothStep 1 = 1 ∧
      graphSmoothStepSlope 0 = 0 ∧ graphSmoothStepSlope 1 = 0 ∧
      graphSmoothStepCurvature 0 = 0 ∧ graphSmoothStepCurvature 1 = 0 := by
  norm_num [graphSmoothStep, graphSmoothStepSlope, graphSmoothStepCurvature]

theorem graphSmoothStep_strictMonoOn : StrictMonoOn graphSmoothStep (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    (by unfold graphSmoothStep; fun_prop : Continuous graphSmoothStep).continuousOn
  intro s hs
  rw [interior_Icc] at hs
  rw [(graphSmoothStep_hasDerivAt s).deriv]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hs.1))
    (sq_pos_of_pos (sub_pos.mpr hs.2))

theorem graphSmoothStep_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    graphSmoothStep s ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← graphSmoothStep_endpoints.1]
    exact graphSmoothStep_strictMonoOn.monotoneOn ⟨le_rfl, zero_le_one⟩ hs hs.1
  · rw [← graphSmoothStep_endpoints.2.1]
    exact graphSmoothStep_strictMonoOn.monotoneOn hs ⟨zero_le_one, le_rfl⟩ hs.2

theorem graphSmoothStep_mem_interior {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    graphSmoothStep s ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · rw [← graphSmoothStep_endpoints.1]
    exact graphSmoothStep_strictMonoOn ⟨le_rfl, zero_le_one⟩ (Ioo_subset_Icc_self hs) hs.1
  · rw [← graphSmoothStep_endpoints.2.1]
    exact graphSmoothStep_strictMonoOn (Ioo_subset_Icc_self hs) ⟨zero_le_one, le_rfl⟩ hs.2

end TimeTraps.Analysis
