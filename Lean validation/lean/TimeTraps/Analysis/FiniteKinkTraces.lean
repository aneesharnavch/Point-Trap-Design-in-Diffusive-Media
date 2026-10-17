module

public import TimeTraps.Analysis.FiniteKinkCalculus

@[expose] public section

/-! One-sided derivatives and the exact derivative jump of a finite-kink
potential. Coincident labels contribute their summed coefficient. Thus
each absolute-value coefficient is half its contribution to the jump. -/

namespace TimeTraps.Analysis

open Set

variable {ι : Type*}

noncomputable def finiteKinkRightSlope (F : ℝ → ℝ) (s : Finset ι) (a c : ι → ℝ) (x : ℝ) : ℝ :=
  deriv F x + ∑ i ∈ s, c i * (if x = a i then 1 else Real.sign (x - a i))

noncomputable def finiteKinkLeftSlope (F : ℝ → ℝ) (s : Finset ι) (a c : ι → ℝ) (x : ℝ) : ℝ :=
  deriv F x + ∑ i ∈ s, c i * (if x = a i then -1 else Real.sign (x - a i))

theorem abs_sub_hasDerivWithinAt_right (x a : ℝ) :
    HasDerivWithinAt (fun y : ℝ => |y - a|)
      (if x = a then 1 else Real.sign (x - a)) (Ici x) x := by
  by_cases hx : x = a
  · subst a
    rw [if_pos rfl]
    apply (((hasDerivAt_id x).sub_const x).hasDerivWithinAt (s := Ici x)).congr_of_mem
    · intro y hy
      exact abs_of_nonneg (sub_nonneg.mpr hy)
    · exact mem_Ici.mpr (le_refl x)
  · rw [if_neg hx]
    exact (abs_sub_hasDerivAt_real_sign hx).hasDerivWithinAt

theorem abs_sub_hasDerivWithinAt_left (x a : ℝ) :
    HasDerivWithinAt (fun y : ℝ => |y - a|)
      (if x = a then -1 else Real.sign (x - a)) (Iic x) x := by
  by_cases hx : x = a
  · subst a
    rw [if_pos rfl]
    apply (((hasDerivAt_id x).sub_const x).neg.hasDerivWithinAt (s := Iic x)).congr_of_mem
    · intro y hy
      exact abs_of_nonpos (sub_nonpos.mpr hy)
    · exact mem_Iic.mpr (le_refl x)
  · rw [if_neg hx]
    exact (abs_sub_hasDerivAt_real_sign hx).hasDerivWithinAt

theorem finiteKinkPotential_right_derivative {F : ℝ → ℝ} {x : ℝ}
    (hF : DifferentiableAt ℝ F x) (s : Finset ι) (a c : ι → ℝ) :
    HasDerivWithinAt (finiteKinkPotential F s a c) (finiteKinkRightSlope F s a c x) (Ici x) x := by
  exact hF.hasDerivAt.hasDerivWithinAt.add (HasDerivWithinAt.fun_sum (fun i (_ : i ∈ s) =>
    (abs_sub_hasDerivWithinAt_right x (a i)).const_mul (c i)))

theorem finiteKinkPotential_left_derivative {F : ℝ → ℝ} {x : ℝ}
    (hF : DifferentiableAt ℝ F x) (s : Finset ι) (a c : ι → ℝ) :
    HasDerivWithinAt (finiteKinkPotential F s a c) (finiteKinkLeftSlope F s a c x) (Iic x) x := by
  exact hF.hasDerivAt.hasDerivWithinAt.add (HasDerivWithinAt.fun_sum (fun i (_ : i ∈ s) =>
    (abs_sub_hasDerivWithinAt_left x (a i)).const_mul (c i)))

theorem finiteKinkPotential_derivative_jump (F : ℝ → ℝ) (s : Finset ι) (a c : ι → ℝ) (x : ℝ) :
    finiteKinkRightSlope F s a c x - finiteKinkLeftSlope F s a c x =
      2 * ∑ i ∈ s, if x = a i then c i else 0 := by
  unfold finiteKinkRightSlope finiteKinkLeftSlope
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x = a i <;> simp only [hi, if_true, if_false] <;> ring

end TimeTraps.Analysis
