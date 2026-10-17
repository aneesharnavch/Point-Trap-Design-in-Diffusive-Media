module

public import TimeTraps.Analysis.GraphShiftedContactOperatorWeak
public import TimeTraps.Analysis.GraphSobolevSpaceDense
public import TimeTraps.Analysis.CompactSpectralEigen

@[expose] public section

/-! The actual compact solution operator on the finite edge L2 Hilbert
product. Density of the full vertex-continuous H1 state range separates
arbitrary L2 sources. Conductance may vary on every edge, reactions are
nonnegative, and the ordinary mass shift supplies coercivity. Positivity here is positivity
of the Hilbert quadratic form, with strict positivity for nonzero loads. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.operatorInverse (P : GraphShiftedContactOperatorProblem V E) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  (graphSobolevSpaceStateL P.geometry).comp P.operatorSolution

theorem GraphShiftedContactOperatorProblem.operatorInverse_apply (P : GraphShiftedContactOperatorProblem V E)
    (f : GraphL2Product P.geometry) :
    P.operatorInverse f = graphSobolevSpaceStateL P.geometry (P.operatorSolution f) := rfl

theorem GraphShiftedContactOperatorProblem.operatorInverse_compact (P : GraphShiftedContactOperatorProblem V E) :
    IsCompactOperator P.operatorInverse :=
  (graphSobolevSpaceStateL_compact P.geometry).comp_clm P.operatorSolution

omit [Fintype V] [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.operatorState_orthogonal_zero (P : GraphShiftedContactOperatorProblem V E)
    (f : GraphL2Product P.geometry)
    (hf : ∀ v : GraphSobolevSpace P.geometry,
      inner ℝ (graphSobolevSpaceStateL P.geometry v) f = 0) : f = 0 := by
  have he : (fun g : GraphL2Product P.geometry => inner ℝ g f) = fun _ => 0 :=
    (graphSobolevSpaceStateL_denseRange P.geometry).equalizer
      (continuous_id.inner continuous_const) continuous_const (funext hf)
  have hz : inner ℝ f f = 0 := congrFun he f
  exact inner_self_eq_zero.mp hz

theorem GraphShiftedContactOperatorProblem.operatorInverse_symmetric (P : GraphShiftedContactOperatorProblem V E) :
    P.operatorInverse.IsSymmetric := by
  intro f g
  change inner ℝ (graphSobolevSpaceStateL P.geometry (P.operatorSolution f)) g =
    inner ℝ f (graphSobolevSpaceStateL P.geometry (P.operatorSolution g))
  calc
    _ = inner ℝ g (graphSobolevSpaceStateL P.geometry (P.operatorSolution f)) :=
      real_inner_comm _ _
    _ = P.operatorForm (P.operatorSolution g) (P.operatorSolution f) :=
      (P.operatorSolution_spec g (P.operatorSolution f)).symm
    _ = P.operatorForm (P.operatorSolution f) (P.operatorSolution g) :=
      P.operatorForm_symmetric _ _
    _ = _ := P.operatorSolution_spec f (P.operatorSolution g)

theorem GraphShiftedContactOperatorProblem.operatorInverse_injective (P : GraphShiftedContactOperatorProblem V E) :
    Function.Injective P.operatorInverse := by
  intro f g heq
  have hs : P.operatorSolution f = P.operatorSolution g :=
    graphSobolevSpaceStateL_injective P.geometry heq
  apply sub_eq_zero.mp
  apply P.operatorState_orthogonal_zero (f - g)
  intro v
  rw [real_inner_comm, inner_sub_left, ← P.operatorSolution_spec f v,
    ← P.operatorSolution_spec g v, hs, sub_self]

theorem GraphShiftedContactOperatorProblem.operatorSolution_injective (P : GraphShiftedContactOperatorProblem V E) :
    Function.Injective P.operatorSolution := by
  intro f g h
  apply P.operatorInverse_injective
  exact congrArg (graphSobolevSpaceStateL P.geometry) h

theorem GraphShiftedContactOperatorProblem.operatorInverse_nonneg (P : GraphShiftedContactOperatorProblem V E)
    (f : GraphL2Product P.geometry) : 0 ≤ inner ℝ f (P.operatorInverse f) := by
  rw [P.operatorInverse_apply, ← P.operatorSolution_spec]
  exact P.operatorForm_nonneg _

theorem GraphShiftedContactOperatorProblem.operatorInverse_positive (P : GraphShiftedContactOperatorProblem V E)
    {f : GraphL2Product P.geometry} (hf : f ≠ 0) :
    0 < inner ℝ f (P.operatorInverse f) := by
  have hs : P.operatorSolution f ≠ 0 := by
    intro hz
    apply hf
    apply P.operatorSolution_injective
    simpa only [map_zero] using hz
  obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
  rw [P.operatorInverse_apply, ← P.operatorSolution_spec]
  exact lt_of_lt_of_le (mul_pos (mul_pos hc (norm_pos_iff.mpr hs))
    (norm_pos_iff.mpr hs)) (hb _)

theorem GraphShiftedContactOperatorProblem.operatorCompactPositiveInverse (P : GraphShiftedContactOperatorProblem V E) :
    CompactPositiveInverse P.operatorInverse :=
  ⟨P.operatorInverse_compact, P.operatorInverse_symmetric,
    P.operatorInverse_nonneg, P.operatorInverse_injective⟩

end TimeTraps.Analysis
