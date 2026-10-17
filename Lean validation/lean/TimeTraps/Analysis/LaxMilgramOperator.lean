module

public import TimeTraps.Analysis.LaxMilgram

@[expose] public section

/-! The Lax--Milgram solution depends bounded-linearly on its full dual
source. This packages the previously proved solution as an actual operator. -/

namespace TimeTraps.Analysis

open InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

noncomputable def coerciveFormSolutionL (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) : (V →L[ℝ] ℝ) →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem coerciveFormSolutionL_apply (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (Λ : V →L[ℝ] ℝ) :
    coerciveFormSolutionL B hB Λ = coerciveFormSolution B hB Λ := rfl

theorem coerciveFormSolutionL_spec (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (Λ : V →L[ℝ] ℝ) (v : V) :
    B (coerciveFormSolutionL B hB Λ) v = Λ v :=
  coerciveFormSolution_spec B hB Λ v

end TimeTraps.Analysis
