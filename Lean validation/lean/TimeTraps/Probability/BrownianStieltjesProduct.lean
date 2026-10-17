module

public import TimeTraps.Probability.DyadicStieltjesRightIntegral
public import TimeTraps.Probability.BrownianAEContinuousMultiplierApproximation
public import TimeTraps.Probability.BrownianItoPathwiseLimit
public import TimeTraps.Probability.BrownianIntegralContinuousGlobal

@[expose] public section

/-! Integration by parts for an actual completed Brownian integral and
a bounded continuous adapted weight of the form c-K. The Stieltjes
integral is the actual pathwise measure integral. Exact finite products,
right Stieltjes sums and the original Itô isometry identify the limit;
no stochastic product formula is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H J : ℝ≥0 → Ω → ℝ}
variable {P : Measure Ω} {M : ℝ≥0}

theorem brownianStieltjesProduct_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : brownianTimeCutoff B hBm P T f = f)
    (hJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (hJI : ∀ t, J t =ᵐ[P] brownianIntegralUpTo hB t f)
    (K : Ω → StieltjesFunction ℝ) (c : Ω → ℝ)
    (hHK : ∀ᵐ ω ∂P, ∀ t, H t ω = c ω - K ω t.val) :
    (fun ω => H T ω * J T ω - H 0 ω * J 0 ω) =ᵐ[P]
      (fun ω => brownianIntegral hB
        (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f) ω -
          ∫ r in Ioc (0 : ℝ) T.val, J r.toNNReal ω ∂(K ω).measure) := by
  let S : ℕ → Lp ℝ 2 P := fun n =>
    brownianIntegral hB (brownianAEContinuousProductStep hBm hH M T n f)
  let R : ℕ → Ω → ℝ := fun n ω => -dyadicStieltjesRightSum (K ω) (fun t => J t ω) T n
  let r : Ω → ℝ := fun ω => -(∫ s in Ioc (0 : ℝ) T.val, J s.toNNReal ω ∂(K ω).measure)
  have hR : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 (r ω)) := by
    filter_upwards [hJ] with ω hω
    exact (dyadicStieltjesRightSum_tendsto (K ω) (fun t => J t ω) hω T).neg
  have hfinite (n : ℕ) : (fun ω => H T ω * J T ω - H 0 ω * J 0 ω) =ᵐ[P]
      (fun ω => S n ω + R n ω) := by
    have hnodes : ∀ᵐ ω ∂P, ∀ i : Fin (2 ^ n + 1),
        J (brownianDyadicGrid T n i) ω =
          brownianIntegralUpTo hB (brownianDyadicGrid T n i) f ω :=
      ae_all_iff.mpr (fun i => hJI (brownianDyadicGrid T n i))
    filter_upwards [hHK, hnodes,
      brownianAEContinuousProductStep_integral_ae hB hBm hH hb T n f] with ω hk hj hs
    change H T ω * J T ω - H 0 ω * J 0 ω =
      brownianIntegral hB (brownianAEContinuousProductStep hBm hH M T n f) ω + _
    rw [hs]
    simp only [brownianStepIntegral, ← hj, hk, R]
    exact (dyadicStieltjes_product_identity (K ω) (fun t => J t ω) (c ω) T n).trans
      (sub_eq_add_neg _ _)
  have he := ae_eq_lp_limit_of_pathwise_remainder S
    (brownianIntegral hB (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f))
    R r (fun ω => H T ω * J T ω - H 0 ω * J 0 ω)
    (brownianAEContinuousProductStepIntegral_tendsto hB hBm hH hjoint hb hcont T f hf) hR hfinite
  exact he

theorem brownianIntegralGlobalPath_stieltjes_product_ae
    {H : ℝ≥0 → (ℕ → ℝ) → ℝ}
    (hH : ∀ t, AEStronglyMeasurable[
      brownianNaturalFiltration brownianDyadicPath brownianDyadicPath_measurable t]
        (H t) brownianDyadicMeasure)
    (hjoint : Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂brownianDyadicMeasure, Continuous (fun t => H t ω)) (T : ℝ≥0)
    (f : BrownianIntegrand)
    (hf : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure T f = f)
    (K : (ℕ → ℝ) → StieltjesFunction ℝ) (c : (ℕ → ℝ) → ℝ)
    (hHK : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t, H t ω = c ω - K ω t.val) :
    (fun ω => H T ω * brownianIntegralGlobalPath f T ω -
      H 0 ω * brownianIntegralGlobalPath f 0 ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (brownianAEContinuousMultiplier brownianDyadicPath_isPreBrownianReal
          brownianDyadicPath_measurable hH hjoint hb hcont f) ω -
        ∫ r in Ioc (0 : ℝ) T.val, brownianIntegralGlobalPath f r.toNNReal ω ∂(K ω).measure) :=
  brownianStieltjesProduct_ae brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    hH hjoint hb hcont T f hf (Filter.Eventually.of_forall (brownianIntegralGlobalPath_continuous f))
    (brownianIntegralGlobalPath_integral_ae f) K c hHK

end TimeTraps.Probability

end
