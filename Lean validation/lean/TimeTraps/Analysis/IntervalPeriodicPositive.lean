module

public import TimeTraps.Analysis.IntervalPeriodicProblem
public import TimeTraps.Analysis.CompactSpectralEigen

@[expose] public section

/-! Symmetry, injectivity and strict positivity of the actual periodic
solution operator. Density of the full periodic H1 state range separates
all L2 forcing terms; positive-contact coercivity supplies positivity. -/

namespace TimeTraps.Analysis

open InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem PeriodicPointProblem.inverse_symmetric (P : PeriodicPointProblem ι l r) :
    P.inverse.IsSymmetric := by
  intro f g
  change inner ℝ (P.boundary.stateL (P.solution f)) g =
    inner ℝ f (P.boundary.stateL (P.solution g))
  calc
    _ = inner ℝ g (P.boundary.stateL (P.solution f)) := real_inner_comm _ _
    _ = P.form (P.solution g) (P.solution f) := (P.solution_spec g (P.solution f)).symm
    _ = P.form (P.solution f) (P.solution g) := P.form_symmetric _ _
    _ = _ := P.solution_spec f (P.solution g)

theorem PeriodicPointProblem.inverse_injective (P : PeriodicPointProblem ι l r) :
    Function.Injective P.inverse := by
  intro f g heq
  have hs : P.solution f = P.solution g := P.boundary.stateL_injective heq
  apply sub_eq_zero.mp
  apply P.boundary.stateL_orthogonal_zero (f - g)
  intro v
  rw [real_inner_comm, inner_sub_left, ← P.solution_spec f v,
    ← P.solution_spec g v, hs, sub_self]

theorem PeriodicPointProblem.solution_injective (P : PeriodicPointProblem ι l r) :
    Function.Injective P.solution := by
  intro f g h
  apply P.inverse_injective
  exact congrArg P.boundary.stateL h

theorem PeriodicPointProblem.inverse_nonneg (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : 0 ≤ inner ℝ f (P.inverse f) := by
  obtain ⟨c, hc, hb⟩ := P.form_coercive
  rw [P.inverse_apply, ← P.solution_spec]
  exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)

theorem PeriodicPointProblem.inverse_positive (P : PeriodicPointProblem ι l r)
    {f : IntervalSobolevL2 l r} (hf : f ≠ 0) : 0 < inner ℝ f (P.inverse f) := by
  have hs : P.solution f ≠ 0 := by
    intro hz
    apply hf
    apply P.solution_injective
    simpa only [map_zero] using hz
  obtain ⟨c, hc, hb⟩ := P.form_coercive
  rw [P.inverse_apply, ← P.solution_spec]
  exact lt_of_lt_of_le (mul_pos (mul_pos hc (norm_pos_iff.mpr hs))
    (norm_pos_iff.mpr hs)) (hb _)

theorem PeriodicPointProblem.compactPositiveInverse (P : PeriodicPointProblem ι l r) :
    CompactPositiveInverse P.inverse :=
  ⟨P.inverse_compact, P.inverse_symmetric, P.inverse_nonneg, P.inverse_injective⟩

end TimeTraps.Analysis
