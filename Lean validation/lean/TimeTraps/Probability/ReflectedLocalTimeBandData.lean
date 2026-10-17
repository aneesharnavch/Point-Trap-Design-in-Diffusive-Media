module

public import TimeTraps.Probability.BrownianLocalTimeBandData
public import TimeTraps.Probability.ReflectedInteriorOccupationIdentity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Genuine reflected occupation bands are ordinary time integrals of
the particle path. They have continuous time paths and equal spatial
averages of the established occupation density on one all-time event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem brownianBandOccupation_continuous {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (a h : ℝ) (ω : Ω) : Continuous (fun T => brownianBandOccupation B a h T ω) := by
  let q : ℝ → ℝ≥0 × Ω := fun s => (s.toNNReal, ω)
  have hq : Measurable q := measurable_real_toNNReal.prodMk measurable_const
  have hm : Measurable (fun s : ℝ => brownianBandIndicator a h (B s.toNNReal ω)) :=
    (brownianBandIndicator_measurable a h).comp (hjoint.comp hq)
  have hi (u v : ℝ) : IntervalIntegrable (fun s : ℝ => brownianBandIndicator a h (B s.toNNReal ω)) volume u v := by
    have hj : IntegrableOn (fun s : ℝ => brownianBandIndicator a h (B s.toNNReal ω)) (uIcc u v) volume :=
      (integrableOn_const (C := (1 : ℝ)) (μ := volume) (s := uIcc u v) isCompact_uIcc.measure_ne_top).mono' hm.aestronglyMeasurable
        (Eventually.of_forall (fun s => brownianBandIndicator_abs_le_one a h (B s.toNNReal ω)))
    exact hj.intervalIntegrable
  exact ((intervalIntegral.continuous_primitive hi 0).comp NNReal.continuous_coe).const_mul (1 / (2 * h))

noncomputable def reflectedOccupationBand (L D x a h : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  brownianBandOccupation (foldedTrajectory L D x brownianDyadicPath) a h T ω

theorem reflectedOccupationBand_continuous (L D x a h : ℝ) (ω : ℕ → ℝ) :
    Continuous (fun T => reflectedOccupationBand L D x a h T ω) :=
  brownianBandOccupation_continuous
    (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable) a h ω

theorem reflectedOccupationBand_jointlyMeasurable (L D x a h : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedOccupationBand L D x a h p.1 p.2) := by
  apply measurable_uncurry_of_continuous_of_measurable (reflectedOccupationBand_continuous L D x a h)
  intro T
  exact measurable_const.mul (brownianItoDrift_bounded_measurable (brownianBandIndicator_measurable a h)
    (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable) T)

theorem reflectedOccupationBand_spatial_average_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ h : ℝ,
      IntegrableOn (foldedOccupationDensity L D x T ω) (Ioo (a - h) (a + h)) volume ∧
      reflectedOccupationBand L D x a h T ω =
        (1 / (2 * h)) * ∫ b in Ioo (a - h) (a + h), foldedOccupationDensity L D x T ω b := by
  filter_upwards [foldedOccupationDensity_bounded_occupation_all_times_ae] with ω hω T h
  have ho := hω T L hL D hD x (brownianBandIndicator a h)
    (brownianBandIndicator_measurable a h) 1 (brownianBandIndicator_abs_le_one a h)
  have he : (fun b => brownianBandIndicator a h b * foldedOccupationDensity L D x T ω b) =
      (Ioo (a - h) (a + h)).indicator (foldedOccupationDensity L D x T ω) := by
    funext b
    by_cases hb : b ∈ Ioo (a - h) (a + h)
    · simp only [brownianBandIndicator, indicator_of_mem hb, one_mul]
    · simp only [brownianBandIndicator, indicator_of_notMem hb, zero_mul]
  rw [he] at ho
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).mp ho.1, ?_⟩
  rw [integral_indicator measurableSet_Ioo] at ho
  exact congrArg (fun r : ℝ => (1 / (2 * h)) * r) ho.2.2.symm

end TimeTraps.Probability
