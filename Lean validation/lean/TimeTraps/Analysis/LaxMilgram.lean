module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
The functional version of Lax--Milgram used in the foundational chapter,
including its quantitative estimate. The solution is constructed from the
proved Riesz and coercive-form equivalences, with no solution hypothesis.
-/

namespace TimeTraps.Analysis

open InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

noncomputable def coerciveFormSolution (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (Λ : V →L[ℝ] ℝ) : V :=
  hB.continuousLinearEquivOfBilin.symm ((toDual ℝ V).symm Λ)

theorem coerciveFormSolution_spec (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (Λ : V →L[ℝ] ℝ) (v : V) :
    B (coerciveFormSolution B hB Λ) v = Λ v := by
  rw [← hB.continuousLinearEquivOfBilin_apply, coerciveFormSolution,
    ContinuousLinearEquiv.apply_symm_apply, toDual_symm_apply]

/-- Every bounded linear source has exactly one weak solution for a bounded
coercive bilinear form on a real Hilbert space. Symmetry is not required. -/
theorem coercive_form_existsUnique (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (Λ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, B u v = Λ v := by
  refine ⟨coerciveFormSolution B hB Λ, coerciveFormSolution_spec B hB Λ, ?_⟩
  intro u hu
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hB.continuousLinearEquivOfBilin_apply, hB.continuousLinearEquivOfBilin_apply,
    hu v, coerciveFormSolution_spec]

omit [CompleteSpace V] in
/-- The usual a priori bound retains the explicit positive coercivity
constant, for application to min(D/3,κ/2) on the unit interval. -/
theorem coercive_form_solution_bound (B : V →L[ℝ] V →L[ℝ] ℝ)
    (Λ : V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hcoerce : ∀ v : V, c * ‖v‖ ^ 2 ≤ B v v)
    {u : V} (hu : ∀ v : V, B u v = Λ v) : ‖u‖ ≤ ‖Λ‖ / c := by
  have h := hcoerce u
  rw [hu u] at h
  have hΛ : Λ u ≤ ‖Λ‖ * ‖u‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using Λ.le_opNorm u)
  rcases eq_or_lt_of_le (norm_nonneg u) with hz | hp
  · rw [← hz]
    exact div_nonneg (norm_nonneg _) hc.le
  · apply (le_div_iff₀ hc).mpr
    nlinarith

end TimeTraps.Analysis
