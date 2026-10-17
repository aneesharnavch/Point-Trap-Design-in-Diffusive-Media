module

public import TimeTraps.Probability.ReflectedRobinEndpointMeasure

@[expose] public section

/-! The full Robin hazard measure has the original interior strengths
and endpoint strengths beta/D against the actual boundary regulators.
Its weighted contact identity holds simultaneously for every continuous
time weight, spatial test and finite horizon. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

def reflectedRobinHazardTimeMeasure (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (ω : ℕ → ℝ) : Measure ℝ :=
  reflectedAtomicHazardTimeMeasure L hL D hD x (reflectedRobinSite L a)
    (reflectedRobinStrength κ β₀ βL) (reflectedRobinStrength_nonneg hκ hβ₀ hβL) ω

omit [Fintype ι] in
theorem reflectedRobinSite_mem {L : ℝ} (hL : 0 ≤ L) {a : ι → ℝ}
    (ha : ∀ i, a i ∈ Icc 0 L) : ∀ i, reflectedRobinSite L a i ∈ Icc 0 L := by
  intro i
  cases i with
  | inl i => exact ha i
  | inr b =>
    cases b with
    | false => exact ⟨le_rfl, hL⟩
    | true => exact ⟨hL, le_rfl⟩

theorem reflectedRobinHazardTimeMeasure_Ioc
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L
      (reflectedRobinSite L a i) ω) (S T : ℝ) :
    reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω (Ioc S T) =
      ENNReal.ofReal (reflectedRobinHazard L D x a κ β₀ βL T.toNNReal ω -
        reflectedRobinHazard L D x a κ β₀ βL S.toNNReal ω) := by
  unfold reflectedRobinHazardTimeMeasure
  rw [reflectedAtomicHazardTimeMeasure_Ioc L hL D hD x _ _ _ hω,
    ← reflectedRobinHazard_eq_atomic L hD, ← reflectedRobinHazard_eq_atomic L hD]

theorem reflectedRobinHazardTimeMeasure_weighted_contact
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (ha : ∀ i, a i ∈ Icc 0 L) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L
      (reflectedRobinSite L a i) ω)
    (hr : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun r => w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))
      (Ioc (0 : ℝ) T.val) (reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) ∧
    (∫ r in Ioc (0 : ℝ) T.val,
      w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
      ∂reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) =
      (∑ i, κ i * g (a i) * ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂reflectedInteriorOccupationTimeMeasure x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω) +
      (β₀ / D) * g 0 * (∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂affineBrownianRegulatorTimeMeasure x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω) +
      (βL / D) * g L * (∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂affineBrownianRegulatorTimeMeasure x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 1 ω) := by
  have he := reflectedRobinAtomicMeasure_weighted_contact L hL D hD x
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
    (reflectedRobinStrength_nonneg hκ hβ₀ hβL) (reflectedRobinSite_mem hL.le ha) hω w hw g T
  refine ⟨he.1, he.2.trans ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [reflectedRobinSite, reflectedRobinStrength, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  rw [reflectedRobinEndpointIntegral_left hL hD (hω (Sum.inr false)) hr,
    reflectedRobinEndpointIntegral_right hL hD (hω (Sum.inr true)) hr]
  ring

theorem reflectedRobinHazardTimeMeasure_weighted_contact_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (ha : ∀ i, a i ∈ Icc 0 L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ w : ℝ≥0 → ℝ, Continuous w → ∀ g : ℝ → ℝ, ∀ T : ℝ≥0,
    IntegrableOn (fun r => w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))
      (Ioc (0 : ℝ) T.val) (reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) ∧
    (∫ r in Ioc (0 : ℝ) T.val,
      w r.toNNReal * g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
      ∂reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) =
      (∑ i, κ i * g (a i) * ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂reflectedInteriorOccupationTimeMeasure x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω) +
      (β₀ / D) * g 0 * (∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂affineBrownianRegulatorTimeMeasure x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω) +
      (βL / D) * g L * (∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal
        ∂affineBrownianRegulatorTimeMeasure x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 1 ω) := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι ⊕ Bool,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (reflectedRobinSite L a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L
      (reflectedRobinSite L a i))
  filter_upwards [hall, affineBrownianLatticeRegular_ae x (Real.sqrt (2 * D)) L] with ω hω hr
  exact fun w hw g T => reflectedRobinHazardTimeMeasure_weighted_contact
    L hL D hD x a κ hκ β₀ βL hβ₀ hβL ha hω hr w hw g T

end TimeTraps.Probability

end
