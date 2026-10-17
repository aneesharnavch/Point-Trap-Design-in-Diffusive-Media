module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Integrand
public import TimeTraps.Probability.BrownianIntegralContinuousGlobalCompact
public import TimeTraps.Probability.BrownianJointMeasurability

@[expose] public section

/-! Canonical continuous horizon paths for the actual original-Brownian
finite-kink integral, with fixed-time identification, raw AE adaptation,
and simultaneous compatibility on a pair of compact horizons. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

def reflectedFiniteKinkC2HorizonPath {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)

theorem reflectedFiniteKinkC2HorizonPath_continuous {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t ω) :=
  brownianIntegralGlobalPath_continuous _ ω

theorem reflectedFiniteKinkC2HorizonPath_jointlyMeasurable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T p.1 p.2) :=
  brownianIntegralGlobalPath_jointlyMeasurable _

theorem reflectedFiniteKinkC2HorizonPath_integral_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T t : ℝ≥0) :
    reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegral (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x (min t T)) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T) t
  change reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t =ᵐ[brownianDyadicMeasure]
    brownianStochasticIntegral (brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure t (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) at he
  rw [reflectedFiniteKinkC2Integrand_cutoff] at he
  exact he

theorem reflectedFiniteKinkC2HorizonPath_raw_aestronglyMeasurable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t)
      brownianDyadicMeasure :=
  brownianIntegralGlobalPath_raw_aestronglyMeasurable _ t

theorem reflectedFiniteKinkC2HorizonPath_zero_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T 0 =ᵐ[brownianDyadicMeasure] (fun _ => 0) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T) 0
  rw [brownianIntegralUpTo_zero] at he
  exact he.trans (Lp.coeFn_zero ℝ 2 brownianDyadicMeasure)

theorem reflectedFiniteKinkC2HorizonPath_compatible {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ S →
      reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x S t ω = reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t ω := by
  have ht (t : BrownianCompactTime S) :
      reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x S t.val =ᵐ[brownianDyadicMeasure]
        reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t.val := by
    have hs := reflectedFiniteKinkC2HorizonPath_integral_ae hF L hL D hD a c ha x S t.val
    have hh := reflectedFiniteKinkC2HorizonPath_integral_ae hF L hL D hD a c ha x T t.val
    rw [min_eq_left t.property.2] at hs
    rw [min_eq_left (t.property.2.trans hST)] at hh
    exact hs.trans hh.symm
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x S (denseSeq (BrownianCompactTime S) n).val ω =
        reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T (denseSeq (BrownianCompactTime S) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime S) n))
  filter_upwards [hall] with ω hω t hts
  have he := (denseRange_denseSeq (BrownianCompactTime S)).equalizer
    ((reflectedFiniteKinkC2HorizonPath_continuous hF L hL D hD a c ha x S ω).comp continuous_subtype_val)
    ((reflectedFiniteKinkC2HorizonPath_continuous hF L hL D hD a c ha x T ω).comp continuous_subtype_val) (funext hω)
  exact congrFun he ⟨t, zero_le, hts⟩

end TimeTraps.Probability

end
