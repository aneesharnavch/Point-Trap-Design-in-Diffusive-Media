module

public import TimeTraps.Probability.ReversibleResistanceCanonicalLocalTimeContact
public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzMeasure

@[expose] public section

/-! Transport to the canonical particle-path additive functional. Its
literal Stieltjes contact integral is identified on the same all-time
good-path event; the completed and original Brownian expectations agree. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceCanonicalLocalTime_integrable (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    Integrable (reversibleResistanceCanonicalLocalTime A x a T) brownianCompletedMeasure := by
  have hi := completedMeasure_integrable brownianDyadicMeasure
    ((reversibleResistanceLocalTime_memLp_two A x a T).integrable (by norm_num))
  apply hi.congr
  filter_upwards [reversibleResistanceCanonicalLocalTime_identification A x ha] with ω hω
  exact (hω.2 T).symm

theorem reversibleResistanceCanonicalLocalTime_mean (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    (∫ ω, reversibleResistanceCanonicalLocalTime A x a T ω ∂brownianCompletedMeasure) =
      ∫ ω, reversibleResistanceLocalTime A x a T ω ∂brownianDyadicMeasure := by
  calc
    _ = ∫ ω : BrownianCompletedSample, reversibleResistanceLocalTime A x a T ω ∂brownianCompletedMeasure := by
      apply integral_congr_ae
      filter_upwards [reversibleResistanceCanonicalLocalTime_identification A x ha] with ω hω
      exact hω.2 T
    _ = _ := completedMeasure_integral brownianDyadicMeasure
      (reversibleResistanceLocalTime_memLp_two A x a T).aestronglyMeasurable

def reversibleResistanceCanonicalRevuzContact (A : IntervalMedium) (x a : ℝ)
    (g : ℝ → ℝ) (T : ℝ≥0) (ω : BrownianCompletedSample) : ℝ := by
  classical
  exact if h : HasContinuousOccupationLocalTime a (resistancePhysicalBandMass A a)
      (reversibleResistanceCanonicalPath A x ω) then
    ∫ t in Ioc (0 : ℝ) T.val, g (reversibleResistanceCanonicalPath A x ω t.toNNReal)
      ∂continuousPathLocalTimeMeasure h (fun r hr => (resistancePhysicalBandMass_pos A a hr).le)
  else 0

theorem reversibleResistanceCanonicalRevuzContact_ae (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ g : ℝ → ℝ, ∀ T : ℝ≥0,
      reversibleResistanceCanonicalRevuzContact A x a g T ω =
        g a * reversibleResistanceLocalTime A x a T ω := by
  filter_upwards [reversibleResistanceCanonicalLocalTime_identification A x ha] with ω hi g T
  let hm : ∀ r, 0 < r → 0 ≤ resistancePhysicalBandMass A a r :=
    fun r hr => (resistancePhysicalBandMass_pos A a hr).le
  let ν := continuousPathLocalTimeMeasure hi.1 hm
  have hsupp : ∀ᵐ t ∂ν, t ∈ ν.support := ν.support_mem_ae
  have hc : ∀ᵐ t ∂ν, g (reversibleResistanceCanonicalPath A x ω t.toNNReal) = g a :=
    hsupp.mono (fun t ht => congrArg g ((continuousPathLocalTimeMeasure_support hi.1 hm ht).2))
  have he (t : ℝ≥0) : continuousPathLocalTime a (resistancePhysicalBandMass A a)
      (reversibleResistanceCanonicalPath A x ω) t = reversibleResistanceLocalTime A x a t ω :=
    (hi.1.value_eq t).symm.trans (hi.2 t)
  have hmass : ν (Ioc (0 : ℝ) T.val) = ENNReal.ofReal (reversibleResistanceLocalTime A x a T ω) := by
    have hv := continuousPathLocalTimeMeasure_Ioc hi.1 hm 0 T
    change ν (Ioc (0 : ℝ) T.val) = _ at hv
    rw [hi.1.zero, sub_zero, he T] at hv
    exact hv
  rw [reversibleResistanceCanonicalRevuzContact, dif_pos hi.1]
  change (∫ t in Ioc (0 : ℝ) T.val, g (reversibleResistanceCanonicalPath A x ω t.toNNReal) ∂ν) = _
  rw [integral_congr_ae (ae_restrict_of_ae hc), setIntegral_const, smul_eq_mul, Measure.real, hmass,
    ENNReal.toReal_ofReal (reversibleResistanceLocalTime_nonneg A x a T ω), mul_comm]

end TimeTraps.Probability

end
