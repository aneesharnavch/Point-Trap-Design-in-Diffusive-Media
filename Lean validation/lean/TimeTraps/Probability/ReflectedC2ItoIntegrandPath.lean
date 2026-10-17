module

public import TimeTraps.Probability.ReflectedC2ItoIntegrand
public import TimeTraps.Probability.BrownianIntegralContinuousGlobalCompact
public import TimeTraps.Probability.BrownianJointMeasurability

@[expose] public section

/-! Canonical continuous paths of the original-Brownian integral of
sqrt(2D)*F'(X)*foldSlope. The actual closed-domain coefficient is used;
the path equals its completed Itô integral at every fixed time, and two
finite horizons agree simultaneously throughout their common interval. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def reflectedC2ItoHorizonPath {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath (reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T)

theorem reflectedC2ItoHorizonPath_continuous {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => reflectedC2ItoHorizonPath hF L hL D hD x T t ω) :=
  brownianIntegralGlobalPath_continuous _ ω

theorem reflectedC2ItoHorizonPath_jointlyMeasurable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedC2ItoHorizonPath hF L hL D hD x T p.1 p.2) :=
  brownianIntegralGlobalPath_jointlyMeasurable _

theorem reflectedC2ItoHorizonPath_integral_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T t : ℝ≥0) :
    reflectedC2ItoHorizonPath hF L hL D hD x T t =ᵐ[brownianDyadicMeasure]
      reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL D hD x (min t T) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL D hD x T) t
  rw [reflectedC2ItoIntegral_upTo] at he
  exact he

theorem reflectedC2ItoHorizonPath_raw_aestronglyMeasurable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (reflectedC2ItoHorizonPath hF L hL D hD x T t)
      brownianDyadicMeasure :=
  brownianIntegralGlobalPath_raw_aestronglyMeasurable _ t

theorem reflectedC2ItoHorizonPath_zero_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    reflectedC2ItoHorizonPath hF L hL D hD x T 0 =ᵐ[brownianDyadicMeasure] (fun _ => 0) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL D hD x T) 0
  rw [brownianIntegralUpTo_zero] at he
  exact he.trans (Lp.coeFn_zero ℝ 2 brownianDyadicMeasure)

theorem reflectedC2ItoHorizonPath_compatible {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ S →
      reflectedC2ItoHorizonPath hF L hL D hD x S t ω = reflectedC2ItoHorizonPath hF L hL D hD x T t ω := by
  have ht (t : BrownianCompactTime S) :
      reflectedC2ItoHorizonPath hF L hL D hD x S t.val =ᵐ[brownianDyadicMeasure]
        reflectedC2ItoHorizonPath hF L hL D hD x T t.val := by
    have hs := reflectedC2ItoHorizonPath_integral_ae hF L hL D hD x S t.val
    have hh := reflectedC2ItoHorizonPath_integral_ae hF L hL D hD x T t.val
    rw [min_eq_left t.property.2] at hs
    rw [min_eq_left (t.property.2.trans hST)] at hh
    exact hs.trans hh.symm
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      reflectedC2ItoHorizonPath hF L hL D hD x S (denseSeq (BrownianCompactTime S) n).val ω =
        reflectedC2ItoHorizonPath hF L hL D hD x T (denseSeq (BrownianCompactTime S) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime S) n))
  filter_upwards [hall] with ω hω t hts
  have he := (denseRange_denseSeq (BrownianCompactTime S)).equalizer
    ((reflectedC2ItoHorizonPath_continuous hF L hL D hD x S ω).comp continuous_subtype_val)
    ((reflectedC2ItoHorizonPath_continuous hF L hL D hD x T ω).comp continuous_subtype_val) (funext hω)
  exact congrFun he ⟨t, zero_le, hts⟩

end TimeTraps.Probability

end
