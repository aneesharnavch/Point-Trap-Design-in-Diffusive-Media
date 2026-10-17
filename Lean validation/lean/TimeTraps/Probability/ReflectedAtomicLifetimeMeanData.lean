module

public import TimeTraps.Probability.ReflectedAtomicSurvivalExpectation
public import TimeTraps.Probability.KillingLifetimeMeanAE

@[expose] public section

/-! The literal real-time atomic clock and its strict-threshold lifetime.
Clock regularity is retained on one almost-sure path event. The extended
nonnegative lifetime preserves infinity; no path modification or finite
lifetime assumption is introduced. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

noncomputable def reflectedAtomicClock (L D x : ℝ) (a κ : ι → ℝ)
    (r : ℝ) (ω : ℕ → ℝ) : ℝ :=
  reflectedAtomicHazard L D x a κ r.toNNReal ω

noncomputable def reflectedAtomicLifetime (L D x : ℝ) (a κ : ι → ℝ)
    (p : (ℕ → ℝ) × ℝ) : WithTop ℝ :=
  contactLifetime (reflectedAtomicClock L D x a κ) p

noncomputable def reflectedAtomicLifetimeValue (L D x : ℝ) (a κ : ι → ℝ)
    (p : (ℕ → ℝ) × ℝ) : ℝ≥0∞ :=
  contactLifetimeValue (reflectedAtomicClock L D x a κ) p

theorem reflectedAtomicClock_jointlyMeasurable (L D x : ℝ) (a κ : ι → ℝ) :
    Measurable (Function.uncurry (reflectedAtomicClock L D x a κ)) := by
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have h := (reflectedAtomicHazard_jointlyMeasurable L D x a κ).comp hm
  have he : Function.uncurry (reflectedAtomicClock L D x a κ) =
      ((fun p : ℝ≥0 × (ℕ → ℝ) => reflectedAtomicHazard L D x a κ p.1 p.2) ∘
        fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) := rfl
  rw [he]
  exact h

theorem reflectedAtomicClock_nonneg (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (r : ℝ) (ω : ℕ → ℝ) :
    0 ≤ reflectedAtomicClock L D x a κ r ω :=
  reflectedAtomicHazard_nonneg L hD x a κ hκ r.toNNReal ω

theorem reflectedAtomicClock_paths_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      ContinuousOn (fun r => reflectedAtomicClock L D x a κ r ω) (Ici (0 : ℝ)) ∧
      MonotoneOn (fun r => reflectedAtomicClock L D x a κ r ω) (Ici (0 : ℝ)) := by
  filter_upwards [reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω
  exact ⟨(hω.1.comp continuous_real_toNNReal).continuousOn,
    (hω.2.1.comp Real.toNNReal_monotone).monotoneOn _⟩

theorem reflectedAtomicSurvival_lintegral (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (reflectedAtomicSurvival L D x a κ T ω) ∂brownianDyadicMeasure) =
      ENNReal.ofReal (reflectedAtomicMeanSurvival L D x a κ T) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (reflectedAtomicSurvival_integrable L hD x a κ hκ T)
    (Eventually.of_forall (fun ω => (reflectedAtomicSurvival_bounds L hD x a κ hκ T ω).1.le))).symm

end TimeTraps.Probability
