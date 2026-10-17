module

public import TimeTraps.Analysis.ReflectedInteriorTanakaFinite
public import TimeTraps.Probability.BrownianAffineItoTanakaC2
public import TimeTraps.Probability.BrownianBoundedIntegrandLimit

@[expose] public section

/-! Each finite folded-kink approximation has an actual closed Brownian
integrand obtained from the already-proved affine finite-kink formula.
Its coefficient has the uniform physical bound sigma. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedInteriorFiniteCoefficient (L a x σ : ℝ) (N : ℕ) (b : ℝ) : ℝ :=
  σ * reflectedInteriorTanakaSlopeApprox L a N (x + σ * b)

noncomputable def reflectedInteriorFiniteIntegrand (L a x σ : ℝ) (N : ℕ) (T : ℝ≥0) : BrownianIntegrand :=
  brownianAffineFiniteKinkC2Integrand (F := fun _ => (0 : ℝ)) contDiff_const
    (M₂ := 0) (by intro y; simp)
    (reflectedInteriorFiniteSet N) (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff x σ T

theorem reflectedInteriorFiniteCoefficient_measurable (L a x σ : ℝ) (N : ℕ) :
    Measurable (reflectedInteriorFiniteCoefficient L a x σ N) := by
  have hm : Measurable (fun b : ℝ => x + σ * b) := (measurable_id.const_mul σ).const_add x
  have hs : Measurable (fun z => finiteKinkSlope (fun _ => (0 : ℝ)) (reflectedInteriorFiniteSet N)
      (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff z) := by
    simp only [finiteKinkSlope, deriv_const, zero_add]
    exact Finset.measurable_sum _ (fun i _ =>
      (brownianSign_measurable.comp (measurable_id.sub_const _)).const_mul _)
  have he : (fun z => finiteKinkSlope (fun _ => (0 : ℝ)) (reflectedInteriorFiniteSet N)
      (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff z) =
      reflectedInteriorTanakaSlopeApprox L a N := funext (reflectedInteriorFinite_slope L a N)
  rw [he] at hs
  exact (hs.comp hm).const_mul σ

theorem reflectedInteriorFiniteCoefficient_bound (L a x : ℝ) {σ : ℝ}
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) (hσ : 0 < σ) (N : ℕ) (b : ℝ) :
    |reflectedInteriorFiniteCoefficient L a x σ N b| ≤ σ := by
  rw [reflectedInteriorFiniteCoefficient, abs_mul, abs_of_pos hσ]
  exact (mul_le_mul_of_nonneg_left
    (reflectedInteriorTanakaSlopeApprox_bound L a N (x + σ * b) hL ha) hσ.le).trans_eq (mul_one σ)

theorem reflectedInteriorFiniteCoefficient_tendsto (L a x : ℝ) {σ : ℝ}
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) (b : ℝ) :
    Tendsto (fun N => reflectedInteriorFiniteCoefficient L a x σ N b) atTop
      (𝓝 (σ * reflectedInteriorTanakaSlope L a (x + σ * b))) := by
  exact (reflectedInteriorTanakaSlopeApprox_tendsto L a (x + σ * b) hL ha).const_mul σ

theorem reflectedInteriorFiniteIntegrand_coe (L a x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (N : ℕ) (T : ℝ≥0) :
    (reflectedInteriorFiniteIntegrand L a x σ N T : Lp ℝ 2 (volume.prod brownianDyadicMeasure))
      =ᵐ[volume.prod brownianDyadicMeasure]
        brownianBoundedProcess brownianDyadicPath (reflectedInteriorFiniteCoefficient L a x σ N) T := by
  filter_upwards [brownianAffineFiniteKinkC2Integrand_coe (F := fun _ => (0 : ℝ)) contDiff_const
    (M₂ := 0) (by intro y; simp) (reflectedInteriorFiniteSet N)
    (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff x hσ T] with p hp
  rw [reflectedInteriorFinite_slope] at hp
  exact hp

end TimeTraps.Probability
