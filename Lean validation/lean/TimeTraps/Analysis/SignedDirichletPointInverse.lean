module

public import TimeTraps.Analysis.SignedDirichletPointProblem
public import TimeTraps.Analysis.CompactSpectralEigen

@[expose] public section

/-! The shifted solution inverse is compact, symmetric, injective and
strictly positive. Its injectivity follows from density of actual
selected-zero H1 states in L2, with arbitrary real or empty contacts. -/

namespace TimeTraps.Analysis

open InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedDirichletPointProblem.shiftedInverse_symmetric (P : SignedDirichletPointProblem ι l r) :
    P.shiftedInverse.IsSymmetric := by
  intro f g
  change inner ℝ (P.boundary.stateL (P.shiftedSolution f)) g =
    inner ℝ f (P.boundary.stateL (P.shiftedSolution g))
  calc
    _ = inner ℝ g (P.boundary.stateL (P.shiftedSolution f)) := real_inner_comm _ _
    _ = P.shiftedForm (P.shiftedSolution g) (P.shiftedSolution f) := (P.shiftedSolution_spec g (P.shiftedSolution f)).symm
    _ = P.shiftedForm (P.shiftedSolution f) (P.shiftedSolution g) := P.shiftedForm_symmetric _ _
    _ = _ := P.shiftedSolution_spec f (P.shiftedSolution g)

theorem SignedDirichletPointProblem.shiftedInverse_injective (P : SignedDirichletPointProblem ι l r) :
    Function.Injective P.shiftedInverse := by
  intro f g heq
  have hs : P.shiftedSolution f = P.shiftedSolution g := P.boundary.stateL_injective heq
  apply sub_eq_zero.mp
  apply P.boundary.stateL_orthogonal_zero (f - g)
  intro v
  rw [real_inner_comm, inner_sub_left, ← P.shiftedSolution_spec f v,
    ← P.shiftedSolution_spec g v, hs, sub_self]

theorem SignedDirichletPointProblem.shiftedSolution_injective (P : SignedDirichletPointProblem ι l r) :
    Function.Injective P.shiftedSolution := by
  intro f g h
  apply P.shiftedInverse_injective
  exact congrArg P.boundary.stateL h

theorem SignedDirichletPointProblem.shiftedInverse_nonneg (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : 0 ≤ inner ℝ f (P.shiftedInverse f) := by
  obtain ⟨c, hc, hb⟩ := P.shiftedForm_coercive
  rw [P.shiftedInverse_apply, ← P.shiftedSolution_spec]
  exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)

theorem SignedDirichletPointProblem.shiftedInverse_positive (P : SignedDirichletPointProblem ι l r)
    {f : IntervalSobolevL2 l r} (hf : f ≠ 0) : 0 < inner ℝ f (P.shiftedInverse f) := by
  have hs : P.shiftedSolution f ≠ 0 := by
    intro hz
    apply hf
    apply P.shiftedSolution_injective
    simpa only [map_zero] using hz
  obtain ⟨c, hc, hb⟩ := P.shiftedForm_coercive
  rw [P.shiftedInverse_apply, ← P.shiftedSolution_spec]
  exact lt_of_lt_of_le (mul_pos (mul_pos hc (norm_pos_iff.mpr hs))
    (norm_pos_iff.mpr hs)) (hb _)

theorem SignedDirichletPointProblem.shiftedCompactPositiveInverse (P : SignedDirichletPointProblem ι l r) :
    CompactPositiveInverse P.shiftedInverse :=
  ⟨P.shiftedInverse_compact, P.shiftedInverse_symmetric, P.shiftedInverse_nonneg, P.shiftedInverse_injective⟩

end TimeTraps.Analysis
