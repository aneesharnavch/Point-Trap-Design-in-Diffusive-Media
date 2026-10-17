module

public import TimeTraps.Analysis.FiniteQuadraticVariation
public import TimeTraps.Probability.BrownianIntegralSquareFinite

@[expose] public section

/-! Continuous monotone paths have vanishing dyadic quadratic variation
on each compact horizon. Their difference therefore does not affect the
quadratic variation of an affine stochastic term. These are deterministic
path statements and impose no integrability on the regulators. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def dyadicPathQV (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  finiteQuadraticVariation (fun i => f (brownianDyadicGrid T n i))

theorem brownianDyadicQV_eq_path {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    brownianDyadicQV B T n ω = dyadicPathQV (fun t => B t ω) T n := rfl

theorem brownianDyadicGrid_mem_Icc (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n + 1)) :
    brownianDyadicGrid T n i ∈ Icc 0 T := by
  refine ⟨zero_le, ?_⟩
  simpa only [brownianDyadicGrid_last] using brownianDyadicGrid_monotone T n (Fin.le_last i)

theorem dyadicPathQV_continuous_monotone_tendsto (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ContinuousOn f (Icc 0 T)) (hm : MonotoneOn f (Icc 0 T)) :
    Tendsto (dyadicPathQV f T) atTop (𝓝 0) := by
  let V : ℝ := f T - f 0
  have hV : 0 ≤ V := sub_nonneg.mpr (hm ⟨le_rfl, zero_le⟩ ⟨zero_le, le_rfl⟩ zero_le)
  have hmesh : Tendsto (fun n : ℕ => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (finiteQuadraticVariation_nonneg _))
  · intro ε hε
    let η : ℝ := ε / (V + 1)
    have hden : 0 < V + 1 := by linarith
    have hη : 0 < η := div_pos hε hden
    obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
    filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn
    have hinc (i : Fin (2 ^ n)) :
        f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc) ≤ η := by
      have hd : dist (brownianDyadicGrid T n i.succ) (brownianDyadicGrid T n i.castSucc) < δ := by
        change |(brownianDyadicGrid T n i.succ).val - (brownianDyadicGrid T n i.castSucc).val| < δ
        rw [brownianDyadicGrid_gap]
        exact hn
      have he := hc _ (brownianDyadicGrid_mem_Icc T n i.succ)
        _ (brownianDyadicGrid_mem_Icc T n i.castSucc) hd
      rw [Real.dist_eq] at he
      exact (le_abs_self _).trans he.le
    have hmono : Monotone (fun i : Fin (2 ^ n + 1) => f (brownianDyadicGrid T n i)) := by
      intro i j hij
      exact hm (brownianDyadicGrid_mem_Icc T n i) (brownianDyadicGrid_mem_Icc T n j)
        (brownianDyadicGrid_monotone T n hij)
    have hb := finiteQuadraticVariation_monotone_bound
      (fun i => f (brownianDyadicGrid T n i)) hmono hinc
    rw [brownianDyadicGrid_last, brownianDyadicGrid_zero] at hb
    have hηeq : η * (V + 1) = ε := div_mul_cancel₀ ε hden.ne'
    change dyadicPathQV f T n < ε
    change dyadicPathQV f T n ≤ η * V at hb
    exact hb.trans_lt (by nlinarith)

theorem dyadicPathQV_affine_regulators_tendsto (f lower upper : ℝ≥0 → ℝ)
    (T : ℝ≥0) (a c A : ℝ)
    (hf : Tendsto (dyadicPathQV f T) atTop (𝓝 A))
    (hlc : ContinuousOn lower (Icc 0 T)) (hlm : MonotoneOn lower (Icc 0 T))
    (huc : ContinuousOn upper (Icc 0 T)) (hum : MonotoneOn upper (Icc 0 T)) :
    Tendsto (dyadicPathQV (fun t => c + a * f t + lower t - upper t) T)
      atTop (𝓝 (a ^ 2 * A)) := by
  have hl := dyadicPathQV_continuous_monotone_tendsto lower T hlc hlm
  have hu := dyadicPathQV_continuous_monotone_tendsto upper T huc hum
  have hr := finiteQuadraticVariation_sub_tendsto_zero (fun n => 2 ^ n)
    (fun n i => lower (brownianDyadicGrid T n i)) (fun n i => upper (brownianDyadicGrid T n i)) hl hu
  have ha : Tendsto (fun n => finiteQuadraticVariation
      (fun i => c + a * f (brownianDyadicGrid T n i))) atTop (𝓝 (a ^ 2 * A)) := by
    have ht := hf.const_mul (a ^ 2)
    change Tendsto (fun n => a ^ 2 * finiteQuadraticVariation
      (fun i => f (brownianDyadicGrid T n i))) atTop (𝓝 (a ^ 2 * A)) at ht
    simpa only [finiteQuadraticVariation_affine] using ht
  have hs := finiteQuadraticVariation_add_tendsto (fun n => 2 ^ n)
    (fun n i => c + a * f (brownianDyadicGrid T n i))
    (fun n i => lower (brownianDyadicGrid T n i) - upper (brownianDyadicGrid T n i))
    (a ^ 2 * A) ha hr
  change Tendsto (fun n => finiteQuadraticVariation
    (fun i => c + a * f (brownianDyadicGrid T n i) + lower (brownianDyadicGrid T n i) -
      upper (brownianDyadicGrid T n i))) atTop (𝓝 (a ^ 2 * A))
  simpa only [add_sub_assoc] using hs

end TimeTraps.Probability
