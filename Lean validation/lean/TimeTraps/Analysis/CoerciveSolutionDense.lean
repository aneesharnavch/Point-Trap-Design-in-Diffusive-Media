module

public import TimeTraps.Analysis.LaxMilgramOperator
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

/-! A symmetric coercive weak solution map has dense range in the energy
space whenever the physical state inclusion is injective. This derives
energy-space density from the full weak equation, not a spectral premise. -/

namespace TimeTraps.Analysis

open InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem coerciveSolution_orthogonal_zero
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B)
    (hSym : ∀ u v, B u v = B v u)
    (J : H →L[ℝ] K) (hJ : Function.Injective J) (S : K →L[ℝ] H)
    (hS : ∀ f v, B (S f) v = inner ℝ f (J v))
    (w : H) (hw : ∀ f, inner ℝ (S f) w = 0) : w = 0 := by
  let v := coerciveFormSolutionL B hB (toDual ℝ H w)
  have hv (u : H) : B v u = inner ℝ w u := coerciveFormSolutionL_spec B hB _ u
  have hj : J v = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    calc
      inner ℝ (J v) (J v) = B (S (J v)) v := (hS _ _).symm
      _ = B v (S (J v)) := hSym _ _
      _ = inner ℝ w (S (J v)) := hv _
      _ = inner ℝ (S (J v)) w := real_inner_comm _ _
      _ = 0 := hw _
  have hz : v = 0 := hJ (hj.trans (map_zero J).symm)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [← hv w, hz, map_zero B, zero_apply]

theorem coerciveSolution_denseRange
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B)
    (hSym : ∀ u v, B u v = B v u)
    (J : H →L[ℝ] K) (hJ : Function.Injective J) (S : K →L[ℝ] H)
    (hS : ∀ f v, B (S f) v = inner ℝ f (J v)) : DenseRange S := by
  have horth : S.toLinearMap.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro w hw
    change w = 0
    apply coerciveSolution_orthogonal_zero B hB hSym J hJ S hS w
    intro f
    exact (S.toLinearMap.range.mem_orthogonal w).mp hw (S f) ⟨f, rfl⟩
  have hcl : S.toLinearMap.range.topologicalClosure = ⊤ :=
    S.toLinearMap.range.topologicalClosure_eq_top_iff.mpr horth
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hcl

end TimeTraps.Analysis
