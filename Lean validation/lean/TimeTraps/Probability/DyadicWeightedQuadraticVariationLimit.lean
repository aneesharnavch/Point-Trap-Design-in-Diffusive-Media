module

public import TimeTraps.Probability.DyadicWeightedQuadraticVariationApproximation

@[expose] public section

/-! Uniform convergence of actual stopped quadratic variation determines
its continuous-weight limit. Fixed coarse-cell masses converge first;
uniform weight approximation and nonnegative square masses then pass to
arbitrary continuous time weights. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem dyadicCumulativeQV_uniform_of_stopped (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ContinuousOn f (Icc 0 T)) (a : ℝ)
    (hq : TendstoUniformlyOn (stoppedDyadicPathQV f T) (fun s => a * s.val) atTop (Icc 0 T)) :
    TendstoUniformlyOn (dyadicCumulativeQV f T) (fun s => a * s.val) atTop (Icc 0 T) := by
  have he := dyadicStoppedQV_sub_cumulative_uniform f T hf
  rw [real_tendstoUniformlyOn_iff_sub_tendsto] at hq he ⊢
  simp only [sub_zero] at he
  have hh := hq.sub he
  have hid (p : ℕ × ℝ≥0) :
      (stoppedDyadicPathQV f T p.1 p.2 - a * p.2.val) -
        (stoppedDyadicPathQV f T p.1 p.2 - dyadicCumulativeQV f T p.1 p.2) =
        dyadicCumulativeQV f T p.1 p.2 - a * p.2.val := by ring
  simpa only [hid, sub_zero] using hh

theorem dyadicCoarseWeightedQV_tendsto (f g : ℝ≥0 → ℝ) (T : ℝ≥0) (a : ℝ) (m : ℕ)
    (hq : TendstoUniformlyOn (dyadicCumulativeQV f T) (fun s => a * s.val) atTop (Icc 0 T)) :
    Tendsto (dyadicCoarseWeightedQV f g T m) atTop (𝓝 (a * dyadicTimeLeftSum g T m)) := by
  have hj (j : Fin (2 ^ m)) :=
    ((hq.tendsto_at (brownianDyadicGrid_mem_Icc T m j.succ)).sub
      (hq.tendsto_at (brownianDyadicGrid_mem_Icc T m j.castSucc))).const_mul
        (g (brownianDyadicGrid T m j.castSucc))
  have hs := tendsto_finsetSum Finset.univ (fun j _ => hj j)
  have he : (∑ j : Fin (2 ^ m), g (brownianDyadicGrid T m j.castSucc) *
      (a * (brownianDyadicGrid T m j.succ).val - a * (brownianDyadicGrid T m j.castSucc).val)) =
      a * dyadicTimeLeftSum g T m := by
    rw [dyadicTimeLeftSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hs
  exact hs

theorem dyadicWeightedPathQV_tendsto (f g : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T)) (a : ℝ)
    (hq : TendstoUniformlyOn (stoppedDyadicPathQV f T) (fun s => a * s.val) atTop (Icc 0 T)) :
    Tendsto (dyadicWeightedPathQV f g T) atTop
      (𝓝 (a * ∫ r in (0 : ℝ)..T.val, g r.toNNReal)) := by
  by_cases hT : T = 0
  · subst T
    have hz : dyadicWeightedPathQV f g 0 = fun _ => 0 := funext (dyadicWeightedPathQV_zero f g)
    rw [hz]
    change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (a * ∫ r in (0 : ℝ)..0, g r.toNNReal))
    rw [intervalIntegral.integral_same, mul_zero]
    exact tendsto_const_nhds
  have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
  have hc := dyadicCumulativeQV_uniform_of_stopped f T hf a hq
  have htotal : Tendsto (dyadicPathQV f T) atTop (𝓝 (a * T.val)) := by
    simpa only [stoppedDyadicPathQV_terminal] using hq.tendsto_at (show T ∈ Icc 0 T from ⟨zero_le, le_rfl⟩)
  have htime := (dyadicTimeLeftSum_tendsto g T hg).const_mul a
  let C : ℝ := |a * T.val| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlt : a * T.val < C := (le_abs_self (a * T.val)).trans_lt (lt_add_one _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (3 * C)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hC)
  have hηC : η * C = ε / 3 := by dsimp [η]; field_simp
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨m, hm, hmlim⟩ := ((dyadicCoarseWeight_approximation g T hTpos hg hη).and
    (Metric.tendsto_nhds.mp htime (ε / 3) hthird)).exists
  have hcoarse := dyadicCoarseWeightedQV_tendsto f g T a m hc
  filter_upwards [hm, Metric.tendsto_nhds.mp hcoarse (ε / 3) hthird,
    htotal.eventually (gt_mem_nhds hlt)] with n hn hcn hqn
  have he := dyadicWeightedPathQV_coarse_error f g T m n hn
  have hsmall : dist (dyadicWeightedPathQV f g T n) (dyadicCoarseWeightedQV f g T m n) < ε / 3 := by
    rw [Real.dist_eq]
    exact he.trans_lt ((mul_lt_mul_of_pos_left hqn hη).trans_eq hηC)
  calc
    _ ≤ dist (dyadicWeightedPathQV f g T n) (dyadicCoarseWeightedQV f g T m n) +
        dist (dyadicCoarseWeightedQV f g T m n) (a * ∫ r in (0 : ℝ)..T.val, g r.toNNReal) :=
      dist_triangle _ _ _
    _ ≤ dist (dyadicWeightedPathQV f g T n) (dyadicCoarseWeightedQV f g T m n) +
        (dist (dyadicCoarseWeightedQV f g T m n) (a * dyadicTimeLeftSum g T m) +
          dist (a * dyadicTimeLeftSum g T m) (a * ∫ r in (0 : ℝ)..T.val, g r.toNNReal)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by linarith

end TimeTraps.Probability
