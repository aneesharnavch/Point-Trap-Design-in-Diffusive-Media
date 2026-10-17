module

public import TimeTraps.Probability.BrownianFoldTanakaFinite
public import TimeTraps.Probability.BrownianFoldSlopeIntegrand

@[expose] public section

/-! The finite affine sign term is sigma times the actual normalized
stochastic integral of the finite fold slope. All evaluations of L2
classes are justified almost everywhere, including finite sums. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem affineBrownianFoldSignApprox_integral_ae (L x σ : ℝ) (N : ℕ) (T : ℝ≥0) :
    affineBrownianFoldSignApprox L x σ N T =ᵐ[brownianDyadicMeasure]
      (σ • brownianIntegral brownianDyadicPath_isPreBrownianReal
        (brownianFoldSlopeApproxIntegrand brownianDyadicPath_isPreBrownianReal
          brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L x σ N T) :
            Lp ℝ 2 brownianDyadicMeasure) := by
  let S (a : ℝ) : Lp ℝ 2 brownianDyadicMeasure := brownianDyadicSignIntegral ((a - x) / σ) T
  let V (j : ℕ) : Lp ℝ 2 brownianDyadicMeasure := (-1 : ℝ) ^ (j + 1) •
    (S ((j + 1 : ℕ) * L) + S (-((j + 1 : ℕ) * L)))
  let W : Lp ℝ 2 brownianDyadicMeasure := S 0 + ∑ j ∈ Finset.range N, V j
  have hW : brownianIntegral brownianDyadicPath_isPreBrownianReal
      (brownianFoldSlopeApproxIntegrand brownianDyadicPath_isPreBrownianReal
        brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L x σ N T) = W := by
    simpa only [W, V, S, brownianDyadicSignIntegral, brownianDyadicSignIntegrand,
      brownianStochasticIntegral, brownianSignIntegral, neg_mul] using
      brownianFoldSlopeApproxIntegrand_integral brownianDyadicPath_isPreBrownianReal
        brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L x σ N T
  rw [hW]
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ j ∈ Finset.range N,
      V j ω = (-1 : ℝ) ^ (j + 1) *
        (brownianSignIntegralGlobalPath (((j + 1 : ℕ) * L - x) / σ) T ω +
          brownianSignIntegralGlobalPath ((-((j + 1 : ℕ) * L) - x) / σ) T ω) := by
    apply (eventually_all_finset (Finset.range N)).mpr
    intro j _
    filter_upwards [Lp.coeFn_smul ((-1 : ℝ) ^ (j + 1))
      (S ((j + 1 : ℕ) * L) + S (-((j + 1 : ℕ) * L))),
      Lp.coeFn_add (S ((j + 1 : ℕ) * L)) (S (-((j + 1 : ℕ) * L))),
      brownianSignIntegralGlobalPath_integral_ae (((j + 1 : ℕ) * L - x) / σ) T,
      brownianSignIntegralGlobalPath_integral_ae ((-((j + 1 : ℕ) * L) - x) / σ) T]
      with ω hs ha hp hn
    dsimp only [V]
    rw [hs, Pi.smul_apply, smul_eq_mul, ha, Pi.add_apply]
    rw [show S ((j + 1 : ℕ) * L) ω =
      brownianSignIntegralGlobalPath (((j + 1 : ℕ) * L - x) / σ) T ω from hp.symm,
      show S (-((j + 1 : ℕ) * L)) ω =
        brownianSignIntegralGlobalPath ((-((j + 1 : ℕ) * L) - x) / σ) T ω from hn.symm]
  filter_upwards [Lp.coeFn_smul σ W, Lp.coeFn_add (S 0) (∑ j ∈ Finset.range N, V j),
    Lp.coeFn_fun_finsetSum (Finset.range N) V,
    brownianSignIntegralGlobalPath_integral_ae ((0 - x) / σ) T, hall] with ω hs ha hsum hzero hj
  rw [hs, Pi.smul_apply, smul_eq_mul]
  change affineBrownianFoldSignApprox L x σ N T ω = σ * ((S 0 + ∑ j ∈ Finset.range N, V j) ω)
  rw [ha, Pi.add_apply, hsum]
  change affineBrownianFoldSignApprox L x σ N T ω = σ * (S 0 ω + ∑ j ∈ Finset.range N, V j ω)
  rw [show S 0 ω = brownianSignIntegralGlobalPath ((0 - x) / σ) T ω from hzero.symm]
  simp only [affineBrownianFoldSignApprox, affineBrownianSignTerm, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hmem
  rw [hj j hmem]
  ring

theorem affineBrownianFoldSignApprox_memLp (L x σ : ℝ) (N : ℕ) (T : ℝ≥0) :
    MemLp (affineBrownianFoldSignApprox L x σ N T) 2 brownianDyadicMeasure :=
  (Lp.memLp (σ • brownianIntegral brownianDyadicPath_isPreBrownianReal
    (brownianFoldSlopeApproxIntegrand brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L x σ N T))).ae_eq
        (affineBrownianFoldSignApprox_integral_ae L x σ N T).symm

theorem affineBrownianFoldSignApprox_L2_tendsto (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun N => (affineBrownianFoldSignApprox_memLp L x σ N T).toLp
      (affineBrownianFoldSignApprox L x σ N T)) atTop
        (𝓝 (σ • brownianFoldSlopeIntegral brownianDyadicPath_isPreBrownianReal
          brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ T)) := by
  have he (N : ℕ) : (affineBrownianFoldSignApprox_memLp L x σ N T).toLp
      (affineBrownianFoldSignApprox L x σ N T) =
        σ • brownianIntegral brownianDyadicPath_isPreBrownianReal
          (brownianFoldSlopeApproxIntegrand brownianDyadicPath_isPreBrownianReal
            brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L x σ N T) := by
    apply Lp.ext
    exact (affineBrownianFoldSignApprox_memLp L x σ N T).coeFn_toLp.trans
      (affineBrownianFoldSignApprox_integral_ae L x σ N T)
  simp only [he]
  exact (brownianFoldSlopeIntegral_approximation_tendsto brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ T).const_smul σ

end TimeTraps.Probability
