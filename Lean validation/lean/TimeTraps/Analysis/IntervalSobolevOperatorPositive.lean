module

public import TimeTraps.Analysis.IntervalSobolevOperator
public import TimeTraps.Analysis.CompactSpectralEigen

@[expose] public section

/-! Compactness, injectivity, symmetry and strict positive quadratic form
for the actual point-contact solution operator, with no spectral premise. -/

namespace TimeTraps.Analysis

open InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι]

theorem UnitPointProblem.inverse_symmetric (P : UnitPointProblem ι) :
    P.inverse.IsSymmetric := by
  intro f g
  change inner ℝ (P.solution f).state g = inner ℝ f (P.solution g).state
  calc
    inner ℝ (P.solution f).state g = inner ℝ g (P.solution f).state := real_inner_comm _ _
    _ = P.form (P.solution g) (P.solution f) := (P.solution_spec g (P.solution f)).symm
    _ = P.form (P.solution f) (P.solution g) := P.form_symmetric _ _
    _ = inner ℝ f (P.solution g).state := P.solution_spec f (P.solution g)

theorem UnitPointProblem.inverse_injective (P : UnitPointProblem ι) :
    Function.Injective P.inverse := by
  intro f g heq
  have hs : P.solution f = P.solution g := ext_state heq
  apply sub_eq_zero.mp
  apply stateL_orthogonal_zero zero_lt_one (f - g)
  intro v
  change inner ℝ v.state (f - g) = 0
  rw [real_inner_comm, inner_sub_left, ← P.solution_spec f v,
    ← P.solution_spec g v, hs, sub_self]

theorem UnitPointProblem.solution_injective (P : UnitPointProblem ι) :
    Function.Injective P.solution := by
  intro f g h
  apply P.inverse_injective
  exact congrArg (fun u : UnitIntervalSobolev => u.state) h

theorem UnitPointProblem.inverse_nonneg (P : UnitPointProblem ι) (f : UnitIntervalL2) :
    0 ≤ inner ℝ f (P.inverse f) := by
  obtain ⟨c, hc, hb⟩ := P.form_coercive
  rw [P.inverse_apply, ← P.solution_spec]
  exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)

theorem UnitPointProblem.inverse_positive (P : UnitPointProblem ι)
    {f : UnitIntervalL2} (hf : f ≠ 0) : 0 < inner ℝ f (P.inverse f) := by
  have hs : P.solution f ≠ 0 := by
    intro hz
    apply hf
    apply P.solution_injective
    simpa only [map_zero] using hz
  obtain ⟨c, hc, hb⟩ := P.form_coercive
  rw [P.inverse_apply, ← P.solution_spec]
  exact lt_of_lt_of_le (mul_pos (mul_pos hc (norm_pos_iff.mpr hs))
    (norm_pos_iff.mpr hs)) (hb _)

theorem UnitPointProblem.compactPositiveInverse (P : UnitPointProblem ι) :
    CompactPositiveInverse P.inverse :=
  ⟨P.inverse_compact, P.inverse_symmetric, P.inverse_nonneg, P.inverse_injective⟩

end TimeTraps.Analysis
