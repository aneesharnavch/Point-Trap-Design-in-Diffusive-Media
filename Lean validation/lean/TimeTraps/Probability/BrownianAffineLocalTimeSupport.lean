module

public import TimeTraps.Probability.BrownianAffineLocalTimeTanaka

@[expose] public section

/-! One explicit measurable event for each fixed affine level transfers
the Brownian support event and the all-time field agreement. On this event
both affine local-time normalizations are continuous and nondecreasing,
and are locally constant at every time away from the affine level. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

def affineBrownianLocalTimeRegular (x σ a : ℝ) (ω : ℕ → ℝ) : Prop :=
  brownianLocalTimeSampleAgreement ((a - x) / σ) ω ∧
    brownianLocalTimeSupportRegular ((a - x) / σ) ω

theorem affineBrownianLocalTimeRegular_measurableSet (x σ a : ℝ) :
    MeasurableSet {ω | affineBrownianLocalTimeRegular x σ a ω} :=
  (brownianLocalTimeSampleAgreement_measurableSet _).inter
    (brownianLocalTimeSupportRegular_measurableSet _)

theorem affineBrownianLocalTimeRegular_ae (x σ a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, affineBrownianLocalTimeRegular x σ a ω :=
  (brownianLocalTimeSampleAgreement_ae _).and (brownianLocalTimeSupportRegular_ae _)

theorem affineBrownianInput_eq_level_iff (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianInput x σ t ω = a ↔ brownianDyadicPath t ω = (a - x) / σ := by
  rw [eq_div_iff hσ.ne']
  change x + σ * brownianDyadicPath t ω = a ↔ brownianDyadicPath t ω * σ = a - x
  constructor <;> intro h <;> linarith

theorem affineBrownianLocalTimeRegular_values {x σ a : ℝ} {ω : ℕ → ℝ}
    (hω : affineBrownianLocalTimeRegular x σ a ω) (t : ℝ≥0) :
    affineBrownianOccupationDensity x σ a t ω =
        σ⁻¹ * brownianLocalTimeGlobalPath ((a - x) / σ) t ω ∧
      affineBrownianTanakaCorrection x σ a t ω =
        σ * brownianLocalTimeGlobalPath ((a - x) / σ) t ω := by
  simp only [affineBrownianOccupationDensity, affineBrownianTanakaCorrection,
    brownianLocalTimeTimeField_eq_of_sampleAgreement hω.1 t, and_self]

theorem affineBrownianLocalTimeRegular_paths {x σ a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hω : affineBrownianLocalTimeRegular x σ a ω) :
    (Continuous (fun t => affineBrownianOccupationDensity x σ a t ω) ∧
      Monotone (fun t => affineBrownianOccupationDensity x σ a t ω) ∧
      affineBrownianOccupationDensity x σ a 0 ω = 0) ∧
    (Continuous (fun t => affineBrownianTanakaCorrection x σ a t ω) ∧
      Monotone (fun t => affineBrownianTanakaCorrection x σ a t ω) ∧
      affineBrownianTanakaCorrection x σ a 0 ω = 0) := by
  have hd : (fun t => affineBrownianOccupationDensity x σ a t ω) =
      (fun t => σ⁻¹ * brownianLocalTimeGlobalPath ((a - x) / σ) t ω) :=
    funext (fun t => (affineBrownianLocalTimeRegular_values hω t).1)
  have hc : (fun t => affineBrownianTanakaCorrection x σ a t ω) =
      (fun t => σ * brownianLocalTimeGlobalPath ((a - x) / σ) t ω) :=
    funext (fun t => (affineBrownianLocalTimeRegular_values hω t).2)
  have h0 := affineBrownianLocalTimeRegular_values hω 0
  simp only [brownianLocalTimeGlobalPath_zero, mul_zero] at h0
  refine ⟨⟨?_, ?_, h0.1⟩, ⟨?_, ?_, h0.2⟩⟩
  · rw [hd]
    exact continuous_const.mul (brownianLocalTimeGlobalPath_continuous _ _)
  · rw [hd]
    exact (brownianLocalTimeGlobalPath_monotone _ _).const_mul (inv_nonneg.mpr hσ.le)
  · rw [hc]
    exact continuous_const.mul (brownianLocalTimeGlobalPath_continuous _ _)
  · rw [hc]
    exact (brownianLocalTimeGlobalPath_monotone _ _).const_mul hσ.le

theorem affineBrownianLocalTimeRegular_locally_constant {x σ a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hω : affineBrownianLocalTimeRegular x σ a ω) (t : ℝ≥0)
    (ht : affineBrownianInput x σ t ω ≠ a) :
    ∀ᶠ s in 𝓝 t,
      affineBrownianOccupationDensity x σ a s ω = affineBrownianOccupationDensity x σ a t ω ∧
      affineBrownianTanakaCorrection x σ a s ω = affineBrownianTanakaCorrection x σ a t ω := by
  have hne : brownianDyadicPath t ω ≠ (a - x) / σ :=
    fun he => ht ((affineBrownianInput_eq_level_iff x hσ a t ω).mpr he)
  filter_upwards [brownianLocalTimeSupportRegular_locally_constant hω.2 t hne] with s hs
  rw [(affineBrownianLocalTimeRegular_values hω s).1,
    (affineBrownianLocalTimeRegular_values hω t).1,
    (affineBrownianLocalTimeRegular_values hω s).2,
    (affineBrownianLocalTimeRegular_values hω t).2, hs]
  exact ⟨rfl, rfl⟩

end TimeTraps.Probability
