module

public import TimeTraps.Analysis.GraphShiftedContactOperatorContact

@[expose] public section

/-! The actual bounded mass-plus-contact form on the original full graph
H1 space. Coercivity is derived with no positive reaction hypothesis. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.operatorForm
    (P : GraphShiftedContactOperatorProblem V E) :
    GraphSobolevSpace P.geometry →L[ℝ] GraphSobolevSpace P.geometry →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (GraphSobolevSpace P.geometry) :=
    Submodule.seminormedAddCommGroup (graphSobolevSubspace P.geometry)
  letI : NormedSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.normedSpace (graphSobolevSubspace P.geometry)
  let M : GraphSobolevSpace P.geometry →L[ℝ] GraphSobolevSpace P.geometry →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (graphSobolevSpaceStateL P.geometry) (graphSobolevSpaceStateL P.geometry)
  exact M + P.contactForm

theorem GraphShiftedContactOperatorProblem.operatorForm_eq
    (P : GraphShiftedContactOperatorProblem V E) (u w : GraphSobolevSpace P.geometry) :
    P.operatorForm u w = inner ℝ (graphSobolevSpaceStateL P.geometry u)
      (graphSobolevSpaceStateL P.geometry w) + P.contactForm u w := by
  simp only [operatorForm, add_apply, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]

omit [Fintype V] [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.operator_mass_pairing
    (P : GraphShiftedContactOperatorProblem V E) (u w : GraphSobolevSpace P.geometry) :
    inner ℝ (graphSobolevSpaceStateL P.geometry u) (graphSobolevSpaceStateL P.geometry w) =
      ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, P.operatorRep u e x * P.operatorRep w e x :=
  graphSobolevStateL_inner_integral P.geometry u.val w.val

theorem GraphShiftedContactOperatorProblem.operatorForm_apply
    (P : GraphShiftedContactOperatorProblem V E) (u w : GraphSobolevSpace P.geometry) :
    P.operatorForm u w = graphShiftedContactForm P.geometry P.strength
      (P.operatorNodes u) (P.operatorNodes w) (P.operatorRep u) (P.operatorRep w) := by
  rw [P.operatorForm_eq, P.operator_mass_pairing, P.contactForm_apply]
  rfl

theorem GraphShiftedContactOperatorProblem.operatorForm_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (u w : GraphSobolevSpace P.geometry) :
    P.operatorForm u w = P.operatorForm w u := by
  rw [P.operatorForm_eq, P.operatorForm_eq, P.contactForm_symmetric u w,
    real_inner_comm (graphSobolevSpaceStateL P.geometry u) (graphSobolevSpaceStateL P.geometry w)]

theorem GraphShiftedContactOperatorProblem.operatorForm_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) :
    0 ≤ P.operatorForm u u := by
  rw [P.operatorForm_eq]
  exact add_nonneg real_inner_self_nonneg (P.contactForm_nonneg u)

theorem GraphShiftedContactOperatorProblem.operatorForm_coercive
    (P : GraphShiftedContactOperatorProblem V E) :
    @IsCoercive (GraphSobolevSpace P.geometry)
      (Submodule.seminormedAddCommGroup (graphSobolevSubspace P.geometry))
      (Submodule.normedSpace (graphSobolevSubspace P.geometry)) P.operatorForm := by
  obtain ⟨c, hc, hb⟩ := graphShiftedContactForm_norm_coercive P.geometry P.strength P.strength_nonneg
  refine ⟨c, hc, ?_⟩
  intro u
  have h := hb u
  change c * ‖u‖ ^ 2 ≤ graphShiftedContactForm P.geometry P.strength
    (P.operatorNodes u) (P.operatorNodes u) (P.operatorRep u) (P.operatorRep u) at h
  rw [← P.operatorForm_apply u u] at h
  simpa only [pow_two, mul_assoc] using h

end TimeTraps.Analysis
