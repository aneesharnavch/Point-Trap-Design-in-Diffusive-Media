module

public import TimeTraps.Probability.BrownianAEContinuousMultiplierRepresentative

@[expose] public section

/-! Finite adapted step association with almost-everywhere measurable
past coefficients. Bounded representatives are chosen separately at the
finite grid nodes. Both the product coefficient and the stochastic sum
retain the original random variables almost everywhere. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
variable {hBm : ∀ t, Measurable (B t)} {P : Measure Ω} {M : ℝ≥0}

def brownianAEPastStepIntegrand {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i : Fin N, AEStronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i) P)
    (M : ℝ≥0) (f : brownianIntegralSpace B hBm P) : brownianIntegralSpace B hBm P :=
  brownianPastStepIntegrand τ hτ (fun i => brownianBoundedAERepresentative (hξ i) M)
    (fun i => brownianBoundedAERepresentative_stronglyMeasurable (hξ i))
    (fun i => brownianBoundedAERepresentative_bound (hξ i)) f

theorem brownianAEPastStepIntegrand_coe {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i : Fin N, AEStronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i) P)
    (hb : ∀ i ω, |ξ i ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    let S : brownianIntegralSpace B hBm P := @brownianAEPastStepIntegrand Ω mΩ B hBm P N τ hτ ξ (fun i : Fin N => hξ i) M f
    (S : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => brownianStepProcess τ ξ p * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) := by
  dsimp only
  refine (brownianPastStepIntegrand_coe τ hτ
    (fun i => brownianBoundedAERepresentative (hξ i) M)
    (fun i => brownianBoundedAERepresentative_stronglyMeasurable (hξ i))
    (fun i => brownianBoundedAERepresentative_bound (hξ i)) f).trans ?_
  have hall : ∀ᵐ p ∂(volume : Measure ℝ).prod P, ∀ i : Fin N,
      brownianBoundedAERepresentative (hξ i) M p.2 = ξ i p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := P)).ae
      (ae_all_iff.mpr (fun i => brownianBoundedAERepresentative_ae (hξ i) (hb i)))
  filter_upwards [hall] with p hp
  apply congrArg (fun z => z * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p)
  apply Finset.sum_congr rfl
  intro i _
  change brownianIntervalIndicator (τ i.castSucc) (τ i.succ) p.1 * _ =
    brownianIntervalIndicator (τ i.castSucc) (τ i.succ) p.1 * _
  exact congrArg (fun z => brownianIntervalIndicator (τ i.castSucc) (τ i.succ) p.1 * z) (hp i)

theorem brownianAEPastStepIntegrand_integral_ae (hB : IsPreBrownianReal B P)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i : Fin N, AEStronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i) P)
    (hb : ∀ i ω, |ξ i ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    brownianIntegral hB (@brownianAEPastStepIntegrand Ω mΩ B hBm P N τ hτ ξ (fun i : Fin N => hξ i) M f) =ᵐ[P]
      brownianStepIntegral (fun t ω => brownianIntegralUpTo hB t f ω) τ ξ := by
  refine (brownianPastStepIntegrand_integral_ae hB τ hτ
    (fun i => brownianBoundedAERepresentative (hξ i) M)
    (fun i => brownianBoundedAERepresentative_stronglyMeasurable (hξ i))
    (fun i => brownianBoundedAERepresentative_bound (hξ i)) f).trans ?_
  filter_upwards [ae_all_iff.mpr (fun i => brownianBoundedAERepresentative_ae (hξ i) (hb i))]
    with ω hω
  apply Finset.sum_congr rfl
  intro i _
  change brownianBoundedAERepresentative (hξ i) M ω * _ = ξ i ω * _
  rw [hω i]

end TimeTraps.Probability

end
