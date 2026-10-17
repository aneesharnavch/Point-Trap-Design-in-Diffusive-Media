module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Integrand
public import TimeTraps.Probability.BrownianIntegralPastMultiplierStep
public import TimeTraps.Analysis.FiniteKinkCalculus

@[expose] public section

/-! The actual coefficient and finite integral decomposition for a smooth
base plus signed interior kinks. Endpoint slopes aggregate all labels;
no distinctness or nonempty-family assumption is required. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkSlope_zero (F : ℝ → ℝ) (L : ℝ) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) :
    finiteKinkSlope F Finset.univ a c 0 = deriv F 0 - ∑ i, c i := by
  have hs (i : ι) : Real.sign (0 - a i) = -1 :=
    Real.sign_of_neg (sub_neg.mpr (ha i).1)
  simp only [finiteKinkSlope, hs, mul_neg, mul_one, Finset.sum_neg_distrib]
  rfl

theorem reflectedFiniteKinkSlope_right (F : ℝ → ℝ) (L : ℝ) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) :
    finiteKinkSlope F Finset.univ a c L = deriv F L + ∑ i, c i := by
  have hs (i : ι) : Real.sign (L - a i) = 1 :=
    Real.sign_of_pos (sub_pos.mpr (ha i).2)
  simp only [finiteKinkSlope, hs, mul_one]

theorem reflectedFiniteKinkC2Integral_sum_ae (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    brownianStochasticIntegral (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)
      =ᵐ[brownianDyadicMeasure] (fun ω =>
        reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
          brownianDyadicPath_jointly_measurable L hL D hD x T ω +
        ∑ i, c i * reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal
          brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL (a i) (ha i) x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T ω) := by
  let I : Lp ℝ 2 brownianDyadicMeasure := reflectedC2ItoIntegral hF
    brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL D hD x T
  let J : ι → Lp ℝ 2 brownianDyadicMeasure := fun i =>
    reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL (a i) (ha i) x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T
  rw [reflectedFiniteKinkC2Integrand_integral]
  change (I + ∑ i, c i • J i : Lp ℝ 2 brownianDyadicMeasure) =ᵐ[brownianDyadicMeasure] _
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      (c i • J i : Lp ℝ 2 brownianDyadicMeasure) ω = c i * J i ω :=
    ae_all_iff.mpr (fun i => by
      filter_upwards [Lp.coeFn_smul (c i) (J i)] with ω hi
      simpa only [Pi.smul_apply, smul_eq_mul] using hi)
  filter_upwards [Lp.coeFn_add I (∑ i, c i • J i),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • J i), hall] with ω hadd hsum hi
  rw [hadd, Pi.add_apply, hsum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hi i)

theorem reflectedFiniteKinkC2Integrand_coe (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) =ᵐ[volume.prod brownianDyadicMeasure]
      brownianSquareProcess (fun t ω => Real.sqrt (2 * D) *
        finiteKinkSlope F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath t ω) *
        reflectedFoldSlope L (x + Real.sqrt (2 * D) * brownianDyadicPath t ω)) T := by
  let A : BrownianIntegrand := reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T
  let K : ι → BrownianIntegrand := fun i => reflectedInteriorKinkIntegrand
    brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL (a i) (ha i) x
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T
  let b : ι → ℝ × (ℕ → ℝ) → ℝ := fun i p => c i *
    brownianSquareProcess (fun t ω => Real.sqrt (2 * D) *
      Real.sign (reflectedFold L (x + Real.sqrt (2 * D) * brownianDyadicPath t ω) - a i) *
      reflectedFoldSlope L (x + Real.sqrt (2 * D) * brownianDyadicPath t ω)) T p
  have hK (i : ι) : (c i • K i : BrownianIntegrand) =ᵐ[volume.prod brownianDyadicMeasure] b i := by
    filter_upwards [Lp.coeFn_smul (c i)
      (K i : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)),
      reflectedInteriorKinkIntegrand_coe brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL (a i) (ha i) x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T] with p hs hk
    change (c i • (K i : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))) p = _
    rw [hs, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun z => c i * z) hk
  have hsum := brownianIntegralSpace_sum_coe (fun i => c i • K i) b hK
  have hA := reflectedC2ItoIntegrand_coe hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL D hD x T
  change ((A : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) +
      ((∑ i, c i • K i : BrownianIntegrand) :
        Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))) =ᵐ[volume.prod brownianDyadicMeasure] _
  filter_upwards [Lp.coeFn_add (A : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))
    ((∑ i, c i • K i : BrownianIntegrand) :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)), hA, hsum] with p hadd hbase hs
  rw [hadd, Pi.add_apply, hbase, hs]
  simp only [b, brownianSquareProcess, finiteKinkSlope, foldedTrajectory,
    mul_add, Finset.mul_sum]
  ring_nf
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end TimeTraps.Probability
