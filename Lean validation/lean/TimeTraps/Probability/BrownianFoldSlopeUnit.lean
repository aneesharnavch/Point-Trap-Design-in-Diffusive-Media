module

public import TimeTraps.Analysis.ReflectedFoldSlopeRegularity
public import TimeTraps.Probability.BrownianLocalTimeLevelNull

@[expose] public section

/-! The positive-time Gaussian law excludes the entire countable corner
lattice for affine Brownian input. Thus the actual fold slope has square
one and is continuous at the input almost everywhere in time and sample.
Time zero is excluded only by its Lebesgue-null status. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_affine_ne_lattice_eval_ae (hB : IsPreBrownianReal B P)
    (L x : ℝ) {σ : ℝ} (hσ : 0 < σ) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ j : ℤ, x + σ * B t ω ≠ j * L := by
  apply ae_all_iff.mpr
  intro j
  filter_upwards [brownian_eval_ne_level_ae hB ht (((j : ℝ) * L - x) / σ)] with ω hω
  intro he
  apply hω
  apply (eq_div_iff hσ.ne').mpr
  linarith

theorem brownian_affine_ne_lattice_prod_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P, p.1 ∈ Ioc (0 : ℝ) T.val →
      ∀ j : ℤ, x + σ * B p.1.toNNReal p.2 ≠ j * L := by
  have hc : ∀ᵐ p ∂(volume : Measure ℝ).prod P, ∀ j : ℤ,
      p.1 ∈ Ioc (0 : ℝ) T.val → B p.1.toNNReal p.2 ≠ ((j : ℝ) * L - x) / σ :=
    ae_all_iff.mpr (fun j => brownian_positive_time_ne_level_prod_ae hB hjoint (((j : ℝ) * L - x) / σ) T)
  filter_upwards [hc] with p hp ht j
  intro he
  apply hp j ht
  apply (eq_div_iff hσ.ne').mpr
  linarith

theorem brownianFoldSlope_square_prod_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P, p.1 ∈ Ioc (0 : ℝ) T.val →
      reflectedFoldSlope L (x + σ * B p.1.toNNReal p.2) ^ 2 = 1 := by
  filter_upwards [brownian_affine_ne_lattice_prod_ae hB hjoint L x hσ T] with p hp ht
  exact reflectedFoldSlope_square_eq_one L hL _ (hp ht)

theorem brownianFoldSlope_continuousAt_prod_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P, p.1 ∈ Ioc (0 : ℝ) T.val →
      ContinuousAt (reflectedFoldSlope L) (x + σ * B p.1.toNNReal p.2) := by
  filter_upwards [brownian_affine_ne_lattice_prod_ae hB hjoint L x hσ T] with p hp ht
  exact reflectedFoldSlope_continuousAt L hL _ (hp ht)

theorem brownianDyadicFoldSlope_square_prod_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod brownianDyadicMeasure, p.1 ∈ Ioc (0 : ℝ) T.val →
      reflectedFoldSlope L (x + σ * brownianDyadicPath p.1.toNNReal p.2) ^ 2 = 1 :=
  brownianFoldSlope_square_prod_ae brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_jointly_measurable L hL x hσ T

end TimeTraps.Probability
