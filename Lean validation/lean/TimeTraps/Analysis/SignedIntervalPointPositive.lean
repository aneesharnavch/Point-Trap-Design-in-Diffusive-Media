module

public import TimeTraps.Analysis.SignedIntervalPointProblem
public import TimeTraps.Analysis.CompactSpectralEigen

@[expose] public section

/-! Compact, symmetric and strictly positive shifted inverse for arbitrary
finite real point strengths. Its injectivity uses density of the actual H1
states in the original L2 space, independently of a spectral construction. -/

namespace TimeTraps.Analysis

open InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.shiftedInverse_symmetric (P : SignedIntervalPointProblem ι l r) :
    P.shiftedInverse.IsSymmetric := by
  intro f g
  change inner ℝ (P.shiftedSolution f).state g = inner ℝ f (P.shiftedSolution g).state
  calc
    inner ℝ (P.shiftedSolution f).state g = inner ℝ g (P.shiftedSolution f).state := real_inner_comm _ _
    _ = P.shiftedForm (P.shiftedSolution g) (P.shiftedSolution f) :=
      (P.shiftedSolution_spec g (P.shiftedSolution f)).symm
    _ = P.shiftedForm (P.shiftedSolution f) (P.shiftedSolution g) := P.shiftedForm_symmetric _ _
    _ = inner ℝ f (P.shiftedSolution g).state := P.shiftedSolution_spec f (P.shiftedSolution g)

theorem SignedIntervalPointProblem.shiftedInverse_injective (P : SignedIntervalPointProblem ι l r) :
    Function.Injective P.shiftedInverse := by
  intro f g heq
  have hs : P.shiftedSolution f = P.shiftedSolution g := ext_state heq
  apply sub_eq_zero.mp
  apply stateL_orthogonal_zero P.interval_pos (f - g)
  intro v
  change inner ℝ v.state (f - g) = 0
  rw [real_inner_comm, inner_sub_left, ← P.shiftedSolution_spec f v,
    ← P.shiftedSolution_spec g v, hs, sub_self]

theorem SignedIntervalPointProblem.shiftedSolution_injective (P : SignedIntervalPointProblem ι l r) :
    Function.Injective P.shiftedSolution := by
  intro f g h
  apply P.shiftedInverse_injective
  exact congrArg (fun u : IntervalSobolevSpace l r => u.state) h

theorem SignedIntervalPointProblem.shiftedInverse_nonneg (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : 0 ≤ inner ℝ f (P.shiftedInverse f) := by
  obtain ⟨c, hc, hb⟩ := P.shiftedForm_coercive
  rw [P.shiftedInverse_apply, ← P.shiftedSolution_spec]
  exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)

theorem SignedIntervalPointProblem.shiftedInverse_positive (P : SignedIntervalPointProblem ι l r)
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

theorem SignedIntervalPointProblem.shiftedCompactPositiveInverse (P : SignedIntervalPointProblem ι l r) :
    CompactPositiveInverse P.shiftedInverse :=
  ⟨P.shiftedInverse_compact, P.shiftedInverse_symmetric, P.shiftedInverse_nonneg,
    P.shiftedInverse_injective⟩

end TimeTraps.Analysis
