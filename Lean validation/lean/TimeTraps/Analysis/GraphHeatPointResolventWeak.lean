module

public import TimeTraps.Analysis.GraphShiftedContactSolutionDense

@[expose] public section

/-! The full-dual point resolvent of the original mass-shifted graph form.
Point evaluation is the actual continuous graph H1 representative, including
vertices. No edgewise Dirac source is represented as an L2 function. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.pointResolventLoad
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) :
    GraphSobolevSpace P.geometry →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ a).comp (graphRealizedSobolevL P.geometry)

omit [Fintype V] in
theorem GraphShiftedContactOperatorProblem.pointResolventLoad_apply
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (v : GraphSobolevSpace P.geometry) :
    P.pointResolventLoad a v = graphRealizedSobolev P.geometry v a := rfl

noncomputable def GraphShiftedContactOperatorProblem.pointResolventSolution
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) :
    GraphSobolevSpace P.geometry := by
  letI : InnerProductSpace ℝ (GraphSobolevProduct P.geometry) :=
    PiLp.innerProductSpace (fun e : E => IntervalSobolevSpace 0 (P.geometry.length e))
  letI : InnerProductSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.innerProductSpace (graphSobolevSubspace P.geometry)
  exact coerciveFormSolutionL (V := GraphSobolevSpace P.geometry)
    P.operatorForm (by
      obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
      exact ⟨c, hc, fun u => hb u⟩) (P.pointResolventLoad a)

set_option maxHeartbeats 800000 in
theorem GraphShiftedContactOperatorProblem.pointResolventSolution_spec
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (v : GraphSobolevSpace P.geometry) :
    P.operatorForm (P.pointResolventSolution a) v = graphRealizedSobolev P.geometry v a := by
  let : InnerProductSpace ℝ (GraphSobolevProduct P.geometry) :=
    PiLp.innerProductSpace (fun e : E => IntervalSobolevSpace 0 (P.geometry.length e))
  let : InnerProductSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.innerProductSpace (graphSobolevSubspace P.geometry)
  change P.operatorForm ((coerciveFormSolutionL (V := GraphSobolevSpace P.geometry)
    P.operatorForm (by
      obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
      exact ⟨c, hc, fun u => hb u⟩)) (P.pointResolventLoad a)) v = _
  change _ = P.pointResolventLoad a v
  exact coerciveFormSolutionL_spec (V := GraphSobolevSpace P.geometry) P.operatorForm
    (by
      obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
      exact ⟨c, hc, fun u => hb u⟩) (P.pointResolventLoad a) v

theorem GraphShiftedContactOperatorProblem.pointResolventSolution_eq_iff
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (u : GraphSobolevSpace P.geometry) :
    u = P.pointResolventSolution a ↔ ∀ v : GraphSobolevSpace P.geometry,
      P.operatorForm u v = graphRealizedSobolev P.geometry v a := by
  constructor
  · rintro rfl
    exact P.pointResolventSolution_spec a
  · intro h
    have he : P.operatorForm (u - P.pointResolventSolution a) (u - P.pointResolventSolution a) = 0 := by
      rw [map_sub P.operatorForm u (P.pointResolventSolution a), sub_apply,
        h, P.pointResolventSolution_spec, sub_self]
    obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
    have hle := hb (u - P.pointResolventSolution a)
    rw [he] at hle
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hn
    have hp : 0 < ‖u - P.pointResolventSolution a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hle

theorem GraphShiftedContactOperatorProblem.pointResolventSolution_pairing
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (f : GraphL2Product P.geometry) :
    inner ℝ f (graphSobolevSpaceStateL P.geometry (P.pointResolventSolution a)) =
      P.realizedSolutionL f a := by
  rw [← P.operatorSolution_spec, P.operatorForm_symmetric, P.pointResolventSolution_spec]
  rfl

theorem GraphShiftedContactOperatorProblem.pointResolventSolution_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (a x : GraphRealization P.geometry) :
    graphRealizedSobolev P.geometry (P.pointResolventSolution a) x =
      graphRealizedSobolev P.geometry (P.pointResolventSolution x) a := by
  rw [← P.pointResolventSolution_spec x, P.operatorForm_symmetric,
    P.pointResolventSolution_spec]

end TimeTraps.Analysis
