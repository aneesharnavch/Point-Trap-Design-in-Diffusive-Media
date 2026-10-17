module

public import TimeTraps.Analysis.FiniteQuadraticVariationUniform
public import TimeTraps.Probability.BrownianQuadraticVariationStopped

@[expose] public section

/-! On a fixed dyadic grid, stop each node at the observation time.
Continuous monotone regulators have uniformly vanishing squared-increment
sums on the whole compact time interval. Thus uniform quadratic variation
is stable under the actual two-regulator form of reflection. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def stoppedDyadicPathQV (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) : ℝ :=
  finiteQuadraticVariation (fun i => f (min s (brownianDyadicGrid T n i)))

theorem stoppedDyadicPathQV_continuous_monotone_uniform (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ContinuousOn f (Icc 0 T)) (hm : MonotoneOn f (Icc 0 T)) :
    TendstoUniformlyOn (stoppedDyadicPathQV f T) (fun _ => 0) atTop (Icc 0 T) := by
  let V : ℝ := f T - f 0
  have hV : 0 ≤ V := sub_nonneg.mpr (hm ⟨le_rfl, zero_le⟩ ⟨zero_le, le_rfl⟩ zero_le)
  have hmesh : Tendsto (fun n : ℕ => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  have hmem (s : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n + 1)) :
      min s (brownianDyadicGrid T n i) ∈ Icc 0 T :=
    ⟨zero_le, (min_le_right _ _).trans (brownianDyadicGrid_mem_Icc T n i).2⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let η : ℝ := ε / (V + 1)
  have hden : 0 < V + 1 := by linarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn s _hs
  have hinc (i : Fin (2 ^ n)) :
      f (min s (brownianDyadicGrid T n i.succ)) -
        f (min s (brownianDyadicGrid T n i.castSucc)) ≤ η := by
    have hd : dist (min s (brownianDyadicGrid T n i.succ))
        (min s (brownianDyadicGrid T n i.castSucc)) < δ := by
      change |(min s (brownianDyadicGrid T n i.succ)).val -
        (min s (brownianDyadicGrid T n i.castSucc)).val| < δ
      exact (brownianStoppedDyadicGrid_gap_le T s n i).trans_lt hn
    have he := hc _ (hmem s n i.succ) _ (hmem s n i.castSucc) hd
    rw [Real.dist_eq] at he
    exact (le_abs_self _).trans he.le
  have hmono : Monotone (fun i : Fin (2 ^ n + 1) => f (min s (brownianDyadicGrid T n i))) := by
    intro i j hij
    exact hm (hmem s n i) (hmem s n j) (min_le_min_left s (brownianDyadicGrid_monotone T n hij))
  have hb := finiteQuadraticVariation_monotone_bound
    (fun i => f (min s (brownianDyadicGrid T n i))) hmono hinc
  rw [brownianDyadicGrid_last, brownianDyadicGrid_zero,
    min_eq_right (show (0 : ℝ≥0) ≤ s from zero_le)] at hb
  have hlast : f (min s T) ≤ f T := hm ⟨zero_le, min_le_right _ _⟩ ⟨zero_le, le_rfl⟩ (min_le_right _ _)
  have hb' : stoppedDyadicPathQV f T n s ≤ η * V :=
    hb.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hlast (f 0)) hη.le)
  have hηeq : η * (V + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have he : stoppedDyadicPathQV f T n s < ε := hb'.trans_lt (by nlinarith)
  have hnonneg : 0 ≤ stoppedDyadicPathQV f T n s := finiteQuadraticVariation_nonneg _
  simpa only [Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg hnonneg] using he

theorem stoppedDyadicPathQV_affine_regulators_uniform (f lower upper : ℝ≥0 → ℝ)
    (T : ℝ≥0) (a c : ℝ) (A : ℝ≥0 → ℝ)
    (hf : TendstoUniformlyOn (stoppedDyadicPathQV f T) A atTop (Icc 0 T))
    (M : ℝ) (hA : ∀ s ∈ Icc 0 T, A s ≤ M)
    (hlc : ContinuousOn lower (Icc 0 T)) (hlm : MonotoneOn lower (Icc 0 T))
    (huc : ContinuousOn upper (Icc 0 T)) (hum : MonotoneOn upper (Icc 0 T)) :
    TendstoUniformlyOn (stoppedDyadicPathQV (fun t => c + a * f t + lower t - upper t) T)
      (fun s => a ^ 2 * A s) atTop (Icc 0 T) := by
  have hl := stoppedDyadicPathQV_continuous_monotone_uniform lower T hlc hlm
  have hu := stoppedDyadicPathQV_continuous_monotone_uniform upper T huc hum
  have hr := finiteQuadraticVariation_uniform_sub_zero (fun n => 2 ^ n)
    (fun n s i => lower (min s (brownianDyadicGrid T n i)))
    (fun n s i => upper (min s (brownianDyadicGrid T n i))) (Icc 0 T) hl hu
  have ha := finiteQuadraticVariation_uniform_affine (fun n => 2 ^ n)
    (fun n s i => f (min s (brownianDyadicGrid T n i))) (Icc 0 T) A a c hf
  have hs := finiteQuadraticVariation_uniform_add (fun n => 2 ^ n)
    (fun n s i => c + a * f (min s (brownianDyadicGrid T n i)))
    (fun n s i => lower (min s (brownianDyadicGrid T n i)) - upper (min s (brownianDyadicGrid T n i)))
    (Icc 0 T) (fun s => a ^ 2 * A s) ha hr (a ^ 2 * M)
    (fun s hs => mul_le_mul_of_nonneg_left (hA s hs) (sq_nonneg a))
  change TendstoUniformlyOn (fun n s => finiteQuadraticVariation
    (fun i => c + a * f (min s (brownianDyadicGrid T n i)) +
      lower (min s (brownianDyadicGrid T n i)) - upper (min s (brownianDyadicGrid T n i))))
    (fun s => a ^ 2 * A s) atTop (Icc 0 T)
  simpa only [add_sub_assoc] using hs

end TimeTraps.Probability
