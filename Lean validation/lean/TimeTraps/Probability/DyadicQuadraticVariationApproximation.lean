module

public import TimeTraps.Probability.DyadicQuadraticVariationCumulative
public import TimeTraps.Probability.DyadicMonotoneUniform
public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariationUniform

@[expose] public section

/-! For a continuous path the one-partial-cell squared error vanishes
uniformly. Consequently, convergence of stopped quadratic variation at
all dyadic nodes implies actual uniform convergence on the compact
horizon. This is a deterministic statement about the whole sequence. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem dyadicStoppedQV_sub_cumulative_uniform (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ContinuousOn f (Icc 0 T)) :
    TendstoUniformlyOn (fun n s => stoppedDyadicPathQV f T n s - dyadicCumulativeQV f T n s)
      (fun _ => 0) atTop (Icc 0 T) := by
  have hmesh : Tendsto (fun n : ℕ => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn s hs
  by_cases hz : s = 0
  · subst s
    have he : stoppedDyadicPathQV f T n 0 = 0 := by
      unfold stoppedDyadicPathQV finiteQuadraticVariation
      apply Finset.sum_eq_zero
      intro i _
      simp only [min_eq_left (show (0 : ℝ≥0) ≤ brownianDyadicGrid T n i.succ from zero_le),
        min_eq_left (show (0 : ℝ≥0) ≤ brownianDyadicGrid T n i.castSucc from zero_le),
        sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    simpa only [he, dyadicCumulativeQV_zero, sub_self, dist_self] using hε
  · have hspos : 0 < s.val := show (0 : ℝ≥0) < s from pos_iff_ne_zero.mpr hz
    obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n ⟨hspos, hs.2⟩
    have he : stoppedDyadicPathQV f T n s - dyadicCumulativeQV f T n s =
        if brownianDyadicGrid T n i.succ ≤ s then 0 else
          (f s - f (brownianDyadicGrid T n i.castSucc)) ^ 2 :=
      dyadicStoppedQV_sub_cumulative_cell f T n s i hi
    have hd : dist s (brownianDyadicGrid T n i.castSucc) < δ := by
      change |s.val - (brownianDyadicGrid T n i.castSucc).val| < δ
      rw [abs_of_nonneg (sub_nonneg.mpr hi.1.le)]
      calc
        _ ≤ (brownianDyadicGrid T n i.succ).val -
            (brownianDyadicGrid T n i.castSucc).val := sub_le_sub_right hi.2 _
        _ ≤ |(brownianDyadicGrid T n i.succ).val -
            (brownianDyadicGrid T n i.castSucc).val| := le_abs_self _
        _ = T.val / (2 : ℝ) ^ n := brownianDyadicGrid_gap T n i
        _ < δ := hn
    have hinc := hc s hs _ (brownianDyadicGrid_mem_Icc T n i.castSucc) hd
    rw [Real.dist_eq] at hinc
    have hsq : (f s - f (brownianDyadicGrid T n i.castSucc)) ^ 2 < ε := by
      nlinarith [abs_nonneg (f s - f (brownianDyadicGrid T n i.castSucc)),
        sq_abs (f s - f (brownianDyadicGrid T n i.castSucc)), Real.sq_sqrt hε.le]
    rw [Real.dist_eq, zero_sub, abs_neg, he]
    split_ifs
    · simpa only [abs_zero] using hε
    · exact (abs_of_nonneg (sq_nonneg (f s - f (brownianDyadicGrid T n i.castSucc)))).trans_lt hsq

theorem stoppedDyadicPathQV_uniform_of_grid (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ContinuousOn f (Icc 0 T))
    (hgrid : ∀ m : ℕ, ∀ i : Fin (2 ^ m + 1),
      Tendsto (fun n => stoppedDyadicPathQV f T n (brownianDyadicGrid T m i))
        atTop (𝓝 (brownianDyadicGrid T m i).val)) :
    TendstoUniformlyOn (stoppedDyadicPathQV f T) (fun s => s.val) atTop (Icc 0 T) := by
  have he := dyadicStoppedQV_sub_cumulative_uniform f T hf
  have hc : TendstoUniformlyOn (dyadicCumulativeQV f T) (fun s => s.val) atTop (Icc 0 T) := by
    apply dyadic_monotone_tendstoUniformlyOn T (dyadicCumulativeQV f T)
      (fun n => (dyadicCumulativeQV_monotone f T n).monotoneOn _)
    intro m i
    have ht := (hgrid m i).sub (he.tendsto_at (brownianDyadicGrid_mem_Icc T m i))
    have hid (n : ℕ) : stoppedDyadicPathQV f T n (brownianDyadicGrid T m i) -
        (stoppedDyadicPathQV f T n (brownianDyadicGrid T m i) -
          dyadicCumulativeQV f T n (brownianDyadicGrid T m i)) =
          dyadicCumulativeQV f T n (brownianDyadicGrid T m i) := by ring
    simpa only [hid, sub_zero] using ht
  rw [real_tendstoUniformlyOn_iff_sub_tendsto] at he hc ⊢
  simp only [sub_zero] at he
  have ht := he.add hc
  simpa only [sub_add_sub_cancel, zero_add] using ht

end TimeTraps.Probability
