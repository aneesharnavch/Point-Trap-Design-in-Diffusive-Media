module

public import TimeTraps.Probability.BrownianOccupationSpatialIdentity

@[expose] public section

/-! The weak spatial occupation identity for the actual Brownian
Tanaka compensation. Both sides are identified as actual L2 elements;
the right side is the genuine ordinary time integral. This does not
assume or select a jointly spatially continuous pointwise local time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaLevelIntegral_eq_occupationTime (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {g : ℝ → ℝ} (hg : Integrable g) (hgc : Continuous g) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    brownianTanakaLevelIntegral hB hBm hjoint T g =
      brownianItoDriftL2 B g T (by
        have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
        exact brownianItoDrift_bounded_memLp (P := P) hgc.measurable hjoint hb T) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hleft := brownianTanakaSmoothLevelIntegral_tendsto hB hBm hjoint T hg
  have hright := brownianOccupationKernel_timeL2_tendsto (P := P)
    tanakaSmoothingScale_pos tanakaSmoothingScale_tendsto hgc hjoint hb T
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n =>
    (brownianTanakaSmoothLevelIntegral_eq_kernelTime hB hBm hjoint hg hgc.measurable hb T n).symm))

theorem brownianTanakaLevelIntegral_occupation_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {g : ℝ → ℝ} (hg : Integrable g) (hgc : Continuous g) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    brownianTanakaLevelIntegral hB hBm hjoint T g =ᵐ[P] brownianItoDrift B g T := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [brownianTanakaLevelIntegral_eq_occupationTime hB hBm hjoint hg hgc hb T]
  exact brownianItoDriftL2_coe B g T (brownianItoDrift_bounded_memLp (P := P) hgc.measurable hjoint hb T)

theorem brownianTanakaLevelIntegral_occupation_compact_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {g : ℝ → ℝ} (hgc : Continuous g) (hcomp : HasCompactSupport g) (T : ℝ≥0) :
    brownianTanakaLevelIntegral hB hBm hjoint T g =ᵐ[P] brownianItoDrift B g T := by
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hcomp
  exact brownianTanakaLevelIntegral_occupation_ae hB hBm hjoint
    (hgc.integrable_of_hasCompactSupport hcomp) hgc
    (fun x => by simpa only [Real.norm_eq_abs] using hM x) T

theorem brownianDyadicTanakaLevelIntegral_occupation_compact_ae
    {g : ℝ → ℝ} (hgc : Continuous g) (hcomp : HasCompactSupport g) (T : ℝ≥0) :
    brownianDyadicTanakaLevelIntegral T g =ᵐ[brownianDyadicMeasure]
      brownianItoDrift brownianDyadicPath g T :=
  brownianTanakaLevelIntegral_occupation_compact_ae brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable hgc hcomp T

end TimeTraps.Probability
