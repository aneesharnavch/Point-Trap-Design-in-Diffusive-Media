module

public import TimeTraps.Probability.BrownianLocalTimeSpatialIntegral
public import TimeTraps.Probability.BrownianOccupationIdentity

@[expose] public section

/-! The ordinary spatial integral of the jointly measurable local-time
version equals the ordinary Brownian occupation-time integral almost
surely, for every fixed bounded continuous L¹ weight. Compactly
supported continuous weights are included. Both integrations are actual
Bochner integrals of real functions; their integrability is proved in
the preceding bridges. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianLocalTimeLevelVersion_occupation_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {g : ℝ → ℝ} (hg : Integrable g volume) (hgc : Continuous g) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    (fun ω => ∫ a, g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) =ᵐ[P]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (B s.toNNReal ω)) :=
  (brownianLocalTimeLevelVersion_integral_ae hB hBm hjoint T hg).symm.trans
    (brownianTanakaLevelIntegral_occupation_ae hB hBm hjoint hg hgc hb T)

theorem brownianLocalTimeLevelVersion_occupation_compact_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {g : ℝ → ℝ} (hgc : Continuous g) (hcomp : HasCompactSupport g) (T : ℝ≥0) :
    (fun ω => ∫ a, g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) =ᵐ[P]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (B s.toNNReal ω)) :=
  (brownianLocalTimeLevelVersion_integral_ae hB hBm hjoint T
    (hgc.integrable_of_hasCompactSupport hcomp)).symm.trans
    (brownianTanakaLevelIntegral_occupation_compact_ae hB hBm hjoint hgc hcomp T)

theorem brownianDyadicLocalTimeLevelVersion_occupation_ae
    {g : ℝ → ℝ} (hg : Integrable g volume) (hgc : Continuous g) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) :
    (fun ω => ∫ a, g a * brownianDyadicLocalTimeLevelVersion T a ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (brownianDyadicPath s.toNNReal ω)) :=
  brownianLocalTimeLevelVersion_occupation_ae brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable hg hgc hb T

theorem brownianDyadicLocalTimeLevelVersion_occupation_compact_ae
    {g : ℝ → ℝ} (hgc : Continuous g) (hcomp : HasCompactSupport g) (T : ℝ≥0) :
    (fun ω => ∫ a, g a * brownianDyadicLocalTimeLevelVersion T a ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (brownianDyadicPath s.toNNReal ω)) :=
  brownianLocalTimeLevelVersion_occupation_compact_ae brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable hgc hcomp T

end TimeTraps.Probability
