module

public import TimeTraps.Analysis.CompactSpectralSemigroup

@[expose] public section

/-! Symmetry of the actual spectral heat operators, derived by the
complete Hilbert expansion and real diagonal coefficients. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem CompactPositiveInverse.heatSemigroup_symmetric {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (t : ℝ≥0) : (h.heatSemigroup t).IsSymmetric := by
  intro x y
  change inner ℝ (h.heatSemigroup t x) y = inner ℝ x (h.heatSemigroup t y)
  refine (h.eigenbasis.tsum_inner_mul_inner (h.heatSemigroup t x) y).symm.trans
    (Eq.trans ?_ (h.eigenbasis.tsum_inner_mul_inner x (h.heatSemigroup t y)))
  apply tsum_congr
  intro i
  rw [real_inner_comm (h.eigenbasis i) (h.heatSemigroup t x),
    h.heatSemigroup_inner, h.heatSemigroup_inner, real_inner_comm (h.eigenbasis i) x]
  ring

end TimeTraps.Analysis
