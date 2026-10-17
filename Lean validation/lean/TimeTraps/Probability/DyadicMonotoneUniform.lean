module

public import TimeTraps.Probability.BrownianIntegralSquareGrid
public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariation
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-! A deterministic finite-grid sandwich: monotone functions converging
to time at every dyadic node of a compact interval converge uniformly
there. No continuity of the approximating functions is required. -/

namespace TimeTraps.Probability

open Set Filter
open scoped NNReal Topology

theorem dyadic_monotone_tendstoUniformlyOn (T : ℝ≥0) (F : ℕ → ℝ≥0 → ℝ)
    (hmono : ∀ n, MonotoneOn (F n) (Icc 0 T))
    (hgrid : ∀ m : ℕ, ∀ i : Fin (2 ^ m + 1),
      Tendsto (fun n => F n (brownianDyadicGrid T m i)) atTop (𝓝 (brownianDyadicGrid T m i).val)) :
    TendstoUniformlyOn F (fun s => s.val) atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hη : 0 < ε / 3 := by positivity
  have hmesh : Tendsto (fun m : ℕ => T.val / (2 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  obtain ⟨m, hm⟩ := (hmesh.eventually (gt_mem_nhds hη)).exists
  have he : ∀ᶠ n in atTop, ∀ i : Fin (2 ^ m + 1),
      dist (F n (brownianDyadicGrid T m i)) (brownianDyadicGrid T m i).val < ε / 3 := by
    apply eventually_all.mpr
    intro i
    exact (hgrid m i).eventually (Metric.ball_mem_nhds _ hη)
  filter_upwards [he] with n hn s hs
  by_cases hz : s = 0
  · subst s
    have h0 := hn 0
    rw [brownianDyadicGrid_zero] at h0
    rw [dist_comm]
    exact h0.trans (by linarith)
  · have hspos : 0 < s.val := show (0 : ℝ≥0) < s from pos_iff_ne_zero.mpr hz
    obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T m ⟨hspos, hs.2⟩
    have hlo := hmono n (brownianDyadicGrid_mem_Icc T m i.castSucc) hs hi.1.le
    have hhi := hmono n hs (brownianDyadicGrid_mem_Icc T m i.succ) hi.2
    have hl := hn i.castSucc
    have hr := hn i.succ
    rw [Real.dist_eq] at hl hr ⊢
    have hgap := brownianDyadicGrid_gap T m i
    have hg : (brownianDyadicGrid T m i.succ).val -
        (brownianDyadicGrid T m i.castSucc).val < ε / 3 :=
      (le_abs_self _).trans_lt (hgap.trans_lt hm)
    have hl' := abs_lt.mp hl
    have hr' := abs_lt.mp hr
    apply abs_lt.mpr
    constructor <;> linarith [hi.1, hi.2]

end TimeTraps.Probability
