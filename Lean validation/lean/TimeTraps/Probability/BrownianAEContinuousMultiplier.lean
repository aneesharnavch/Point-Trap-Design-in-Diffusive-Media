module

public import TimeTraps.Probability.BrownianAEContinuousMultiplierDomain
public import TimeTraps.Probability.BrownianIntegralTruncationDomain

@[expose] public section

/-! The actual bounded multiplication operator under raw almost-everywhere
adaptation. It acts on the original closed Brownian integrand space,
has the pointwise coefficient and sharp multiplier norm bound, and
commutes with deterministic time cutoff. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {M : ℝ≥0}

def brownianAEContinuousMultiplier
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) :
    brownianIntegralSpace B hBm P →L[ℝ] brownianIntegralSpace B hBm P :=
  (brownianAdaptedContinuousMultiplierAmbient
    (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
    (fun p => hb p.1.toNNReal p.2)).restrict
      (fun _ hf => brownianAEContinuousMultiplier_mem_space hB hBm hH hjoint hb hcont hf)

theorem brownianAEContinuousMultiplier_coe
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (f : brownianIntegralSpace B hBm P) :
    (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => H p.1.toNNReal p.2 * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) := by
  change brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _
  exact brownianAdaptedContinuousMultiplierAmbient_coe
    (brownianAdaptedContinuousMultiplier_raw_measurable hjoint) (fun p => hb p.1.toNNReal p.2)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))

theorem brownianAEContinuousMultiplier_norm
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (f : brownianIntegralSpace B hBm P) :
    ‖brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f‖ ≤ M.val * ‖f‖ := by
  change ‖brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖ ≤
        M.val * ‖(f : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖
  exact brownianAdaptedContinuousMultiplierAmbient_norm
    (brownianAdaptedContinuousMultiplier_raw_measurable hjoint) (fun p => hb p.1.toNNReal p.2)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))

theorem brownianAEContinuousMultiplier_cutoff
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (t : ℝ≥0) (f : brownianIntegralSpace B hBm P) :
    brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont (brownianTimeCutoff B hBm P t f) =
      brownianTimeCutoff B hBm P t (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [brownianAEContinuousMultiplier_coe hB hBm hH hjoint hb hcont
      (brownianTimeCutoff B hBm P t f),
    brownianTimeCutoff_coe t f,
    brownianTimeCutoff_coe t (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f),
    brownianAEContinuousMultiplier_coe hB hBm hH hjoint hb hcont f] with p hm hf ht hp
  rw [hm, hf, ht]
  by_cases hpt : p ∈ brownianTimePast t
  · rw [Set.indicator_of_mem hpt, Set.indicator_of_mem hpt, hp]
  · rw [Set.indicator_of_notMem hpt, Set.indicator_of_notMem hpt, mul_zero]

end TimeTraps.Probability

end
