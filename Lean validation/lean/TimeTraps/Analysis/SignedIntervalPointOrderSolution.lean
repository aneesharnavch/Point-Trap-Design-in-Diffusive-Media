module

public import TimeTraps.Analysis.SignedIntervalPointOrderAbsolute

@[expose] public section

/-! The actual shifted solution of nonnegative L2 forcing equals its
absolute H1 representative. The proof uses preserved quadratic energy,
the sign of the load and the proved coercivity of the explicit mass shift.
Nonnegativity holds at both endpoints as well as in the interior. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.shiftedSolution_eq_orderAbs
    (P : SignedIntervalPointProblem ι l r) (f : IntervalSobolevL2 l r)
    (hf : ∀ᵐ x ∂volume.restrict (Ioo l r), 0 ≤ f x) :
    P.shiftedSolution f = P.orderAbs (P.shiftedSolution f) := by
  let u := P.shiftedSolution f
  let v := P.orderAbs u
  have he : P.shiftedForm (u - v) (u - v) = 2 * P.shiftedForm u (u - v) := by
    simp only [map_sub, sub_apply]
    have hv : P.shiftedForm v v = P.shiftedForm u u := P.shiftedForm_orderAbs u
    rw [P.shiftedForm_symmetric v u, hv]
    ring
  have hn : P.shiftedForm (u - v) (u - v) ≤ 0 := by
    rw [he]
    have hs : P.shiftedForm u (u - v) = inner ℝ f (u - v).state :=
      P.shiftedSolution_spec f (u - v)
    rw [hs]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (P.orderAbs_load_nonpos f hf u)
  obtain ⟨c, hc, hb⟩ := P.shiftedForm_coercive
  have hz := (hb (u - v)).trans hn
  change u = v
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  by_contra hn
  have hp : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hz

theorem SignedIntervalPointProblem.shiftedSolution_representative_nonneg
    (P : SignedIntervalPointProblem ι l r) (f : IntervalSobolevL2 l r)
    (hf : ∀ᵐ x ∂volume.restrict (Ioo l r), 0 ≤ f x) :
    ∀ x ∈ Icc l r, 0 ≤ (P.shiftedSolution f).representative P.interval_pos x := by
  intro x hx
  have he := P.orderAbs_representative (P.shiftedSolution f) hx
  rw [← P.shiftedSolution_eq_orderAbs f hf] at he
  exact he.symm ▸ abs_nonneg ((P.shiftedSolution f).representative P.interval_pos x)

theorem SignedIntervalPointProblem.shiftedInverse_nonneg_ae
    (P : SignedIntervalPointProblem ι l r) (f : IntervalSobolevL2 l r)
    (hf : ∀ᵐ x ∂volume.restrict (Ioo l r), 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict (Ioo l r), 0 ≤ P.shiftedInverse f x := by
  rw [P.shiftedInverse_apply]
  filter_upwards [((P.shiftedSolution f).representative_spec P.interval_pos).2.1,
    ae_restrict_mem measurableSet_Ioo] with x hx hi
  rw [hx]
  exact P.shiftedSolution_representative_nonneg f hf x (Ioo_subset_Icc_self hi)

end TimeTraps.Analysis
