module

public import TimeTraps.Probability.BrownianFoldSlopeApproximation
public import TimeTraps.Probability.BrownianBoundedIntegrandLimit
public import TimeTraps.Analysis.ReflectedFoldTanakaGeometry

@[expose] public section

/-! The actual bounded periodic fold slope, composed with x + sigma B,
belongs to the closed Brownian integrand space by convergence of its
finite sign sums. This constructs the normalized stochastic integral;
it does not assert a reflected-process law or a Levy characterization. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldSlopeIntegrand_exists (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∃ u : brownianIntegralSpace B hBm P,
      ((u : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
        brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T) ∧
      Tendsto (fun N => brownianFoldSlopeApproxIntegrand hB hBm hjoint L x σ N T) atTop (𝓝 u) ∧
      Tendsto (fun N => brownianIntegral hB
        (brownianFoldSlopeApproxIntegrand hB hBm hjoint L x σ N T)) atTop (𝓝 (brownianIntegral hB u)) :=
  brownianBoundedIntegrand_limit hB hBm hjoint (brownianFoldSlopeApprox_measurable L x σ)
    (fun N z => reflectedFoldTanakaSlopeApprox_bound L hL N (x + σ * z))
    (fun z => reflectedFoldTanakaSlopeApprox_tendsto L hL (x + σ * z)) T
    (fun N => brownianFoldSlopeApproxIntegrand hB hBm hjoint L x σ N T)
    (fun N => brownianFoldSlopeApproxIntegrand_coe hB hBm hjoint L x hσ N T)

noncomputable def brownianFoldSlopeIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  Classical.choose (brownianFoldSlopeIntegrand_exists hB hBm hjoint L hL x hσ T)

theorem brownianFoldSlopeIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      =ᵐ[volume.prod P] brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T :=
  (Classical.choose_spec (brownianFoldSlopeIntegrand_exists hB hBm hjoint L hL x hσ T)).1

theorem brownianFoldSlopeIntegrand_approximation_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun N => brownianFoldSlopeApproxIntegrand hB hBm hjoint L x σ N T) atTop
      (𝓝 (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T)) :=
  (Classical.choose_spec (brownianFoldSlopeIntegrand_exists hB hBm hjoint L hL x hσ T)).2.1

noncomputable def brownianFoldSlopeIntegral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) : Lp ℝ 2 P :=
  brownianIntegral hB (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T)

theorem brownianFoldSlopeIntegral_approximation_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun N => brownianIntegral hB
      (brownianFoldSlopeApproxIntegrand hB hBm hjoint L x σ N T)) atTop
      (𝓝 (brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ T)) :=
  (Classical.choose_spec (brownianFoldSlopeIntegrand_exists hB hBm hjoint L hL x hσ T)).2.2

theorem brownianFoldSlopeIntegral_isometry (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (∫ ω, brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ T ω ^ 2 ∂P) =
      ∫ p, (brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2
        ∂(volume : Measure ℝ).prod P := by
  calc
    _ = ∫ p, (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂(volume : Measure ℝ).prod P :=
      brownianIntegral_isometry hB _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [brownianFoldSlopeIntegrand_coe hB hBm hjoint L hL x hσ T] with p hp
      exact congrArg (fun z : ℝ => z ^ 2) hp

end TimeTraps.Probability
