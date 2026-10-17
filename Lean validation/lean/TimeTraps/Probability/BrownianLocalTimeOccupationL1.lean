module

public import TimeTraps.Probability.BrownianOccupationL1Extension
public import TimeTraps.Probability.BrownianLocalTimeSpatialIntegral

@[expose] public section

/-! For every scalar L¹ weight, the actual ordinary spatial integral
of the jointly measurable local-time version equals the actual ordinary
Brownian time integral almost surely. No boundedness, pointwise scalar
measurability, or spatial path continuity is assumed. The identity is
for each fixed weight and finite horizon. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianLocalTimeLevelVersion_occupation_L1_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    (fun ω => ∫ a, g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) =ᵐ[P]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (B s.toNNReal ω)) :=
  (brownianLocalTimeLevelVersion_integral_ae hB hBm hjoint T hg).symm.trans
    (brownianTanakaLevelIntegral_occupation_L1_ae hB hBm hjoint T hg)

theorem brownianDyadicLocalTimeLevelVersion_occupation_L1_ae (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    (fun ω => ∫ a, g a * brownianDyadicLocalTimeLevelVersion T a ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (brownianDyadicPath s.toNNReal ω)) :=
  brownianLocalTimeLevelVersion_occupation_L1_ae brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T hg

end TimeTraps.Probability
