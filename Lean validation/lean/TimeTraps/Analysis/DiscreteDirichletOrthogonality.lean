module

public import TimeTraps.Analysis.DiscreteDirichletCosine
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Exact sine orthogonality and normalization. Orthogonality follows from
the distinct eigenvalues and the symmetric discrete energy identity. -/

namespace TimeTraps.Analysis

open scoped BigOperators

theorem discreteSine_angle_mem {n : ℕ} (k : Fin n) :
    ((k.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) ∈ Set.Ioo 0 Real.pi := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hk : (k.val : ℝ) < n := by exact_mod_cast k.isLt
  constructor
  · exact div_pos (mul_pos (by positivity) Real.pi_pos) hn
  · apply (div_lt_iff₀ hn).mpr
    nlinarith [Real.pi_pos]

theorem discreteSineEigenvalue_strictMono (n : ℕ) : StrictMono (discreteSineEigenvalue n) := by
  intro k l hkl
  have hk := discreteSine_angle_mem k
  have hl := discreteSine_angle_mem l
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hklR : (k.val : ℝ) < l.val := by exact_mod_cast hkl
  have ha : ((k.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) <
      ((l.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) := by
    apply (div_lt_div_iff_of_pos_right hn).mpr
    nlinarith [Real.pi_pos]
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hk.1.le hl.2.le ha
  rw [discreteSineEigenvalue_eq, discreteSineEigenvalue_eq]
  linarith

theorem discreteSineEigenvalue_pos {n : ℕ} (k : Fin n) : 0 < discreteSineEigenvalue n k := by
  have hk := discreteSine_angle_mem k
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 from le_rfl) hk.2.le hk.1
  rw [Real.cos_zero] at hc
  rw [discreteSineEigenvalue_eq]
  linarith

theorem discreteSineMode_bilinear_energy {n : ℕ} (k l : Fin n) :
    (∑ i : Fin (n + 1),
      (discreteSineMode n k i.succ - discreteSineMode n k i.castSucc) *
      (discreteSineMode n l i.succ - discreteSineMode n l i.castSucc)) =
      discreteSineEigenvalue n l * ∑ j, discreteSineVector n k j * discreteSineVector n l j := by
  rw [discrete_dirichlet_summation_by_parts _ _ (discreteSineMode_zero k)
    (discreteSineMode_last k)]
  simp_rw [discreteSineMode_eigenvector]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change discreteSineVector n k j * _ = _
  ring

theorem discreteSineVector_orthogonal {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    (∑ j, discreteSineVector n k j * discreteSineVector n l j) = 0 := by
  have h1 := discreteSineMode_bilinear_energy k l
  have h2 := discreteSineMode_bilinear_energy l k
  have he : (∑ i : Fin (n + 1),
      (discreteSineMode n k i.succ - discreteSineMode n k i.castSucc) *
      (discreteSineMode n l i.succ - discreteSineMode n l i.castSucc)) =
      ∑ i : Fin (n + 1),
      (discreteSineMode n l i.succ - discreteSineMode n l i.castSucc) *
      (discreteSineMode n k i.succ - discreteSineMode n k i.castSucc) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hi : (∑ j, discreteSineVector n l j * discreteSineVector n k j) =
      ∑ j, discreteSineVector n k j * discreteSineVector n l j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, h2, hi] at h1
  have hz : (discreteSineEigenvalue n k - discreteSineEigenvalue n l) *
      (∑ j, discreteSineVector n k j * discreteSineVector n l j) = 0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr ((discreteSineEigenvalue_strictMono n).injective.ne hkl))

noncomputable def discreteNormalizedSine (n : ℕ) (k j : Fin n) : ℝ :=
  Real.sqrt (2 / ((n : ℝ) + 1)) * discreteSineVector n k j

theorem discreteNormalizedSine_symmetric {n : ℕ} (k j : Fin n) :
    discreteNormalizedSine n k j = discreteNormalizedSine n j k := by
  simp only [discreteNormalizedSine, discreteSineVector_symmetric k j]

theorem discreteNormalizedSine_inner_scale {n : ℕ} (k l : Fin n) :
    (∑ j, discreteNormalizedSine n k j * discreteNormalizedSine n l j) =
      (2 / ((n : ℝ) + 1)) * ∑ j, discreteSineVector n k j * discreteSineVector n l j := by
  have hs : (Real.sqrt (2 / ((n : ℝ) + 1))) ^ 2 = 2 / ((n : ℝ) + 1) :=
    Real.sq_sqrt (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold discreteNormalizedSine
  calc
    _ = (Real.sqrt (2 / ((n : ℝ) + 1))) ^ 2 *
        (discreteSineVector n k j * discreteSineVector n l j) := by ring
    _ = _ := by rw [hs]

theorem discreteNormalizedSine_orthonormal {n : ℕ} (k l : Fin n) :
    (∑ j, discreteNormalizedSine n k j * discreteNormalizedSine n l j) =
      if k = l then 1 else 0 := by
  rw [discreteNormalizedSine_inner_scale]
  by_cases hkl : k = l
  · subst l
    simp only [ite_true, ← pow_two, discreteSineVector_norm_sq]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · rw [discreteSineVector_orthogonal hkl, mul_zero, if_neg hkl]

end TimeTraps.Analysis
