module

public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplierDomain
public import TimeTraps.Probability.BrownianIntegralTruncationDomain

@[expose] public section

/-! The actual bounded multiplication operator on the closed Brownian
integrand space. Its stochastic integral is the original completed Itô
integral, with the same norm bound. Deterministic time cutoff commutes
with multiplication, so the construction also respects finite horizons. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {M : ℝ≥0}

def brownianAdaptedContinuousMultiplier
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) :
    brownianIntegralSpace B hBm P →L[ℝ] brownianIntegralSpace B hBm P :=
  (brownianAdaptedContinuousMultiplierAmbient
    (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
    (fun p => hb p.1.toNNReal p.2)).restrict
      (fun _ hf => brownianAdaptedContinuousMultiplier_mem_space hB hBm hH hjoint hb hcont hf)

theorem brownianAdaptedContinuousMultiplier_coe
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (f : brownianIntegralSpace B hBm P) :
    (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => H p.1.toNNReal p.2 * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) := by
  change brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _
  exact brownianAdaptedContinuousMultiplierAmbient_coe
    (brownianAdaptedContinuousMultiplier_raw_measurable hjoint) (fun p => hb p.1.toNNReal p.2)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))

theorem brownianAdaptedContinuousMultiplier_norm
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (f : brownianIntegralSpace B hBm P) :
    ‖brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f‖ ≤ M.val * ‖f‖ := by
  change ‖brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖ ≤
        M.val * ‖(f : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖
  exact brownianAdaptedContinuousMultiplierAmbient_norm
    (brownianAdaptedContinuousMultiplier_raw_measurable hjoint) (fun p => hb p.1.toNNReal p.2)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))

def brownianAdaptedContinuousMultiplierIntegral
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) :
    brownianIntegralSpace B hBm P →L[ℝ] Lp ℝ 2 P :=
  (brownianIntegral hB).toContinuousLinearMap.comp
    (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont)

theorem brownianAdaptedContinuousMultiplierIntegral_norm
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (f : brownianIntegralSpace B hBm P) :
    ‖brownianAdaptedContinuousMultiplierIntegral hB hBm hH hjoint hb hcont f‖ ≤ M.val * ‖f‖ := by
  change ‖brownianIntegral hB (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f)‖ ≤ _
  rw [(brownianIntegral hB).norm_map]
  exact brownianAdaptedContinuousMultiplier_norm hB hBm hH hjoint hb hcont f

theorem brownianAdaptedContinuousMultiplier_cutoff
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (t : ℝ≥0) (f : brownianIntegralSpace B hBm P) :
    brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont (brownianTimeCutoff B hBm P t f) =
      brownianTimeCutoff B hBm P t (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [brownianAdaptedContinuousMultiplier_coe hB hBm hH hjoint hb hcont
      (brownianTimeCutoff B hBm P t f),
    brownianTimeCutoff_coe t f,
    brownianTimeCutoff_coe t (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f),
    brownianAdaptedContinuousMultiplier_coe hB hBm hH hjoint hb hcont f] with p hm hf ht hp
  rw [hm, hf, ht]
  by_cases hpt : p ∈ brownianTimePast t
  · rw [Set.indicator_of_mem hpt, Set.indicator_of_mem hpt, hp]
  · rw [Set.indicator_of_notMem hpt, Set.indicator_of_notMem hpt, mul_zero]

end TimeTraps.Probability

end
