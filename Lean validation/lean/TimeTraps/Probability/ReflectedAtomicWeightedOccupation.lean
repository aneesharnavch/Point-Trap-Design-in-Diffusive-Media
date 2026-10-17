module

public import TimeTraps.Probability.ReflectedAtomicWeightedOccupationData

@[expose] public section

/-! Actual survival-weighted occupation integrals are nonnegative and
bounded by the corresponding actual occupation coefficient. Measurability
comes from literal measurable dyadic sums, and their already proved L²
occupation bound then gives square integrability. Interior sites carry
the occupation interpretation; no random-measure measurability or
stochastic product formula is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicWeightedOccupation_bounds
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (i : ι) {ω : ℕ → ℝ}
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (hc : Continuous (fun t => reflectedAtomicSurvival L D x a κ t ω)) (T : ℝ≥0) :
    0 ≤ reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ∧
      reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ≤
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  let μ := reflectedInteriorOccupationTimeMeasure x hσ hL (a i) ω
  have hmass : μ (Ioc (0 : ℝ) T.val) =
      ENNReal.ofReal (reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω) :=
    reflectedInteriorOccupationTimeMeasure_mass hσ hL hω T
  have : IsFiniteMeasure (μ.restrict (Ioc (0 : ℝ) T.val)) :=
    ⟨by rw [Measure.restrict_apply_univ, hmass]; exact ENNReal.ofReal_lt_top⟩
  have hi : IntegrableOn (fun r : ℝ => reflectedAtomicSurvival L D x a κ r.toNNReal ω)
      (Ioc (0 : ℝ) T.val) μ := by
    rw [show μ = (reflectedInteriorOccupationStieltjes x hσ hL (a i) ω).measure from
      reflectedInteriorOccupationTimeMeasure_eq_stieltjes x hσ hL (a i) ω]
    exact (hc.comp continuous_real_toNNReal).integrableOn_Ioc
  constructor
  · exact integral_nonneg (fun r => (reflectedAtomicSurvival_bounds L hD x a κ hκ r.toNNReal ω).1.le)
  · calc
      _ ≤ ∫ _r in Ioc (0 : ℝ) T.val, (1 : ℝ) ∂μ :=
        integral_mono hi (integrable_const 1)
          (fun r => (reflectedAtomicSurvival_bounds L hD x a κ hκ r.toNNReal ω).2)
      _ = _ := by
        simp only [integral_const, Measure.real, Measure.restrict_apply_univ, hmass, smul_eq_mul, mul_one,
          ENNReal.toReal_ofReal (reflectedInteriorOccupationCoefficient_nonneg x hσ L (a i) T ω)]

theorem reflectedAtomicWeightedOccupation_bounds_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι, ∀ T : ℝ≥0,
      0 ≤ reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ∧
        reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ≤
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [hall, reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω hp
  exact fun i T => reflectedAtomicWeightedOccupation_bounds L hL D hD x a κ hκ i
    (hω i) hp.2.2.2.1 T

theorem reflectedAtomicWeightedOccupation_aestronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (i : ι) (T : ℝ≥0) :
    AEStronglyMeasurable (reflectedAtomicWeightedOccupation L hL D hD x a κ i T)
      brownianDyadicMeasure := by
  let V : (ℕ → ℝ) → ℝ := fun ω =>
    limUnder atTop (fun n => reflectedAtomicWeightedOccupationSum L D x a κ i T n ω)
  refine ⟨V, ?_, ?_⟩
  · exact StronglyMeasurable.limUnder (fun n =>
      (reflectedAtomicWeightedOccupationSum_measurable L D x a κ i T n).stronglyMeasurable)
  · filter_upwards [reflectedAtomicWeightedOccupationSum_tendsto_ae L hL D hD x a κ hκ] with ω hω
    exact (hω i T).limUnder_eq.symm

theorem reflectedAtomicWeightedOccupation_memLp
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (i : ι) (T : ℝ≥0) :
    MemLp (reflectedAtomicWeightedOccupation L hL D hD x a κ i T) 2 brownianDyadicMeasure := by
  apply (reflectedInteriorOccupationCoefficient_memLp L hL D hD x (a i) T).mono'
    (reflectedAtomicWeightedOccupation_aestronglyMeasurable L hL D hD x a κ hκ i T)
  filter_upwards [reflectedAtomicWeightedOccupation_bounds_ae L hL D hD x a κ hκ] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hω i T).1] using (hω i T).2

end TimeTraps.Probability
