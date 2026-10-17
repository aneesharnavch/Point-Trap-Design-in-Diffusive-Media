module

public import TimeTraps.Probability.ReflectedInteriorOccupationConditionalTest
public import TimeTraps.Probability.BrownianIntegralTruncation

@[expose] public section

/-! Conditional algebra for the actual interior occupation coefficient.
The stochastic term has zero future conditional mean by the proved
cutoff identity in the original Brownian integral space. All equalities
are for fixed deterministic times and the original raw filtration. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedInteriorOccupationTestIntegral_condExp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[brownianStochasticIntegral
      (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x t) | brownianFiltration s]
        =ᵐ[brownianDyadicMeasure] brownianStochasticIntegral
          (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x s) := by
  have hc := brownianStochasticIntegralUpTo_condExp s
    (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x t)
  have hcut : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure s
      (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x t) =
        reflectedInteriorOccupationTestIntegrand L hL D hD a ha x s := by
    unfold reflectedInteriorOccupationTestIntegrand
    rw [reflectedFiniteKinkC2Integrand_cutoff, min_eq_left hst]
  have he : brownianStochasticIntegralUpTo s (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x t) =
      brownianStochasticIntegral (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x s) :=
    congrArg brownianStochasticIntegral hcut
  rw [he] at hc
  exact hc

theorem reflectedInteriorOccupationTestIntegral_increment_condExp_zero (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[fun ω =>
      brownianStochasticIntegral (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x t) ω -
      brownianStochasticIntegral (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x s) ω |
        brownianFiltration s] =ᵐ[brownianDyadicMeasure] 0 := by
  have hi (u : ℝ≥0) : Integrable (brownianStochasticIntegral
      (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x u)) brownianDyadicMeasure :=
    (Lp.memLp _).integrable (by norm_num)
  filter_upwards [condExp_sub (hi t) (hi s) (brownianFiltration s),
    reflectedInteriorOccupationTestIntegral_condExp L hL D hD a ha x hst,
    reflectedInteriorOccupationTestIntegral_condExp L hL D hD a ha x (le_refl s)] with ω he ht hs
  simp only [Pi.sub_apply, ht, hs, sub_self] at he
  exact he

theorem reflectedInteriorOccupationTest_raw_stronglyMeasurable (L D x a : ℝ) (s : ℝ≥0) :
    StronglyMeasurable[brownianFiltration s] (fun ω => reflectedInteriorOccupationTest L a
      (foldedTrajectory L D x brownianDyadicPath s ω)) := by
  have hx := foldedTrajectory_adapted brownianFiltration L D x brownianDyadicPath
    (fun t => (brownianFiltration_stronglyAdapted t).measurable) s
  exact ((reflectedInteriorOccupationTest_continuous L a).measurable.comp hx).stronglyMeasurable

theorem reflectedInteriorOccupationCoefficient_increment_condExp_algebra
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[fun ω =>
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t ω -
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a s ω | brownianFiltration s]
        =ᵐ[brownianDyadicMeasure] fun ω =>
      (brownianDyadicMeasure[fun ω => reflectedInteriorOccupationTest L a
          (foldedTrajectory L D x brownianDyadicPath t ω) | brownianFiltration s] ω -
        reflectedInteriorOccupationTest L a (foldedTrajectory L D x brownianDyadicPath s ω) +
          2 * D * (t.val - s.val) / L) / (2 * D) := by
  let V (u : ℝ≥0) (ω : ℕ → ℝ) := reflectedInteriorOccupationTest L a
    (foldedTrajectory L D x brownianDyadicPath u ω)
  let I (u : ℝ≥0) := brownianStochasticIntegral (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x u)
  let E (ω : ℕ → ℝ) := reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t ω -
    reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a s ω
  let c : ℝ := 2 * D * (t.val - s.val) / L
  have hv (u : ℝ≥0) : Integrable (V u) brownianDyadicMeasure :=
    (reflectedInteriorOccupationTest_memLp L hL D x a u).integrable (by norm_num)
  have hi (u : ℝ≥0) : Integrable (I u) brownianDyadicMeasure := (Lp.memLp _).integrable (by norm_num)
  have hconst : Integrable (fun _ : ℕ → ℝ => c) brownianDyadicMeasure := integrable_const c
  have hincr : (fun ω => (2 * D) * E ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => V t ω - V s ω + c - (I t ω - I s ω)) := by
    filter_upwards [reflectedInteriorOccupationTest_formula L hL D hD a ha x t,
      reflectedInteriorOccupationTest_formula L hL D hD a ha x s] with ω ht hs
    dsimp only [V, I, E, c]
    linear_combination hs - ht
  have hp : brownianDyadicMeasure[V s | brownianFiltration s] = V s :=
    condExp_of_stronglyMeasurable (brownianFiltration.le s)
      (reflectedInteriorOccupationTest_raw_stronglyMeasurable L D x a s) (hv s)
  have hconstEq := condExp_const (μ := brownianDyadicMeasure) (brownianFiltration.le s) c
  filter_upwards [condExp_congr_ae hincr,
    condExp_smul (μ := brownianDyadicMeasure) (2 * D) E (brownianFiltration s),
    condExp_sub (((hv t).sub (hv s)).add hconst) ((hi t).sub (hi s)) (brownianFiltration s),
    condExp_add ((hv t).sub (hv s)) hconst (brownianFiltration s),
    condExp_sub (hv t) (hv s) (brownianFiltration s),
    reflectedInteriorOccupationTestIntegral_increment_condExp_zero L hL D hD a ha x hst]
      with ω he hscale hsub hadd hvs hz
  change brownianDyadicMeasure[E | brownianFiltration s] ω = _
  change brownianDyadicMeasure[fun ω => I t ω - I s ω | brownianFiltration s] ω = 0 at hz
  simp only [Pi.smul_apply, smul_eq_mul] at hscale
  simp only [Pi.sub_apply, Pi.add_apply] at hsub hadd hvs
  rw [hp] at hvs
  rw [hconstEq] at hadd
  change brownianDyadicMeasure[fun ω => (2 * D) * E ω | brownianFiltration s] ω =
    (2 * D) * brownianDyadicMeasure[E | brownianFiltration s] ω at hscale
  change brownianDyadicMeasure[fun ω => V t ω - V s ω + c - (I t ω - I s ω) |
      brownianFiltration s] ω =
    brownianDyadicMeasure[fun ω => V t ω - V s ω + c | brownianFiltration s] ω -
      brownianDyadicMeasure[fun ω => I t ω - I s ω | brownianFiltration s] ω at hsub
  change brownianDyadicMeasure[fun ω => V t ω - V s ω + c | brownianFiltration s] ω =
    brownianDyadicMeasure[fun ω => V t ω - V s ω | brownianFiltration s] ω + c at hadd
  change brownianDyadicMeasure[fun ω => V t ω - V s ω | brownianFiltration s] ω =
    brownianDyadicMeasure[V t | brownianFiltration s] ω - V s ω at hvs
  have h2D : (2 * D) ≠ 0 := ne_of_gt (mul_pos (by norm_num) hD)
  apply (eq_div_iff h2D).mpr
  change brownianDyadicMeasure[E | brownianFiltration s] ω * (2 * D) =
    brownianDyadicMeasure[V t | brownianFiltration s] ω - V s ω + c
  calc
    _ = brownianDyadicMeasure[fun ω => (2 * D) * E ω | brownianFiltration s] ω := by
      rw [hscale, mul_comm]
    _ = brownianDyadicMeasure[fun ω => V t ω - V s ω + c | brownianFiltration s] ω -
        brownianDyadicMeasure[fun ω => I t ω - I s ω | brownianFiltration s] ω := he.trans hsub
    _ = _ := by rw [hadd, hvs, hz, sub_zero]

end TimeTraps.Probability
