module

public import TimeTraps.Analysis.IntervalSobolev

@[expose] public section

/-! Integration by parts and finite telescoping for signed slope jumps.
The edge formula has continuous finite one-sided slope traces and an
integrable classical second derivative. All exterior boundary terms remain. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped ContDiff

theorem piecewise_adjacent_sum {n : ℕ} (a : Fin (n + 2) → ℝ) :
    (∑ e : Fin (n + 1), (a e.succ - a e.castSucc)) = a (Fin.last (n + 1)) - a 0 := by
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ a
  have h₁ := Fin.sum_univ_castSucc a
  linarith

theorem piecewise_boundary_sum {n : ℕ} (a b : Fin (n + 1) → ℝ) :
    (∑ e, (a e - b e)) = a 0 - b (Fin.last n) +
      ∑ i : Fin n, (a i.succ - b i.castSucc) := by
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ a, Fin.sum_univ_castSucc b,
    Finset.sum_sub_distrib]
  ring

theorem piecewise_integral_sum {n : ℕ} (q : Fin (n + 2) → ℝ) (hq : Monotone q)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume (q 0) (q (Fin.last (n + 1)))) :
    (∑ e : Fin (n + 1), ∫ x in q e.castSucc..q e.succ, f x) =
      ∫ x in q 0..q (Fin.last (n + 1)), f x := by
  have hi (v : Fin (n + 2)) : IntervalIntegrable f volume (q 0) (q v) := by
    apply hf.mono_set
    apply uIcc_subset_uIcc_left
    rw [uIcc_of_le (hq (Fin.zero_le _))]
    exact ⟨hq (Fin.zero_le v), hq (Fin.le_last v)⟩
  have he (e : Fin (n + 1)) :
      (∫ x in q e.castSucc..q e.succ, f x) =
        (∫ x in q 0..q e.succ, f x) - (∫ x in q 0..q e.castSucc, f x) :=
    (intervalIntegral.integral_interval_sub_left (hi e.succ) (hi e.castSucc)).symm
  simp_rw [he]
  rw [piecewise_adjacent_sum (fun v => ∫ x in q 0..q v, f x),
    intervalIntegral.integral_same, sub_zero]

theorem piecewise_edge_second_green {u j g φ : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hu : ContinuousOn u (Icc l r)) (hj : ContinuousOn j (Icc l r))
    (hg : IntervalIntegrable g volume l r)
    (hdu : ∀ x ∈ Ioo l r, HasDerivAt u (j x) x)
    (hdj : ∀ x ∈ Ioo l r, HasDerivAt j (g x) x)
    (hφ : ContDiff ℝ ∞ φ) :
    (∫ x in l..r, u x * deriv (deriv φ) x) =
      (∫ x in l..r, g x * φ x) + u r * deriv φ r - u l * deriv φ l - j r * φ r + j l * φ l := by
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hiu : IntervalIntegrable (fun x => u x * deriv (deriv φ) x) volume l r :=
    (hu.mul (hφd.continuous_deriv (by simp)).continuousOn).intervalIntegrable_of_Icc hlr
  have hig : IntervalIntegrable (fun x => g x * φ x) volume l r :=
    hg.mul_continuousOn hφ.continuous.continuousOn
  have hc : ContinuousOn (fun x => u x * deriv φ x - j x * φ x) (Icc l r) :=
    (hu.mul hφd.continuous.continuousOn).sub (hj.mul hφ.continuous.continuousOn)
  have hd : ∀ x ∈ Ioo l r, HasDerivAt (fun y => u y * deriv φ y - j y * φ y)
      (u x * deriv (deriv φ) x - g x * φ x) x := by
    intro x hx
    convert! ((hdu x hx).mul ((hφd.differentiable (by simp) x).hasDerivAt)).sub
      ((hdj x hx).mul ((hφ.differentiable (by simp) x).hasDerivAt)) using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr hc hd (hiu.sub hig)
  rw [intervalIntegral.integral_sub hiu hig] at hi
  linarith

end TimeTraps.Analysis
