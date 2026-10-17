module

public import TimeTraps.Probability.ReflectedAtomicWeightedBoundaryData

@[expose] public section

/-! The two actual survival-weighted regulator integrals are nonnegative,
bounded by their actual regulator values, AE measurable, and in L².
Measurability is obtained from the literal dyadic sums; the dominating
regulator moments were derived from the actual quadratic reflected Itô
identities. No random-measure measurability is presumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicWeightedBoundary_bounds
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (b : Fin 2) {ω : ℕ → ℝ}
    (hω : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω)
    (hc : Continuous (fun t => reflectedAtomicSurvival L D x a κ t ω)) (T : ℝ≥0) :
    0 ≤ reflectedAtomicWeightedBoundary L hL D hD x a κ b T ω ∧
      reflectedAtomicWeightedBoundary L hL D hD x a κ b T ω ≤
        affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ) T ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  let μ := affineBrownianRegulatorTimeMeasure x hσ hL (b.val : ℤ) ω
  have hmass : μ (Ioc (0 : ℝ) T.val) =
      ENNReal.ofReal (affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ) T ω) := by
    have he := affineBrownianRegulatorTimeMeasure_Ioc hσ hL hω (b.val : ℤ) 0 T.val
    have hT : T.val.toNNReal = T := Real.toNNReal_coe (r := T)
    have hz : affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ)
        (0 : ℝ).toNNReal ω = 0 := by
      rw [Real.toNNReal_zero]
      exact affineBrownianRegulator_zero hσ hω (b.val : ℤ)
    exact he.trans (congrArg ENNReal.ofReal
      ((congrArg₂ (fun s t : ℝ => s - t)
        (congrArg (fun t : ℝ≥0 =>
          affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ) t ω) hT) hz).trans
        (sub_zero _)))
  have : IsFiniteMeasure (μ.restrict (Ioc (0 : ℝ) T.val)) :=
    ⟨by rw [Measure.restrict_apply_univ, hmass]; exact ENNReal.ofReal_lt_top⟩
  have hi : IntegrableOn (fun r : ℝ => reflectedAtomicSurvival L D x a κ r.toNNReal ω)
      (Ioc (0 : ℝ) T.val) μ := by
    change IntegrableOn (fun r : ℝ => reflectedAtomicSurvival L D x a κ r.toNNReal ω)
      (Ioc (0 : ℝ) T.val) (affineBrownianRegulatorStieltjes x hσ hL (b.val : ℤ) ω).measure
    exact (hc.comp continuous_real_toNNReal).integrableOn_Ioc
  constructor
  · exact integral_nonneg (fun r => (reflectedAtomicSurvival_bounds L hD x a κ hκ r.toNNReal ω).1.le)
  · calc
      _ ≤ ∫ _r in Ioc (0 : ℝ) T.val, (1 : ℝ) ∂μ :=
        integral_mono hi (integrable_const 1)
          (fun r => (reflectedAtomicSurvival_bounds L hD x a κ hκ r.toNNReal ω).2)
      _ = _ := by
        simp only [integral_const, Measure.real, Measure.restrict_apply_univ, hmass, smul_eq_mul, mul_one,
          ENNReal.toReal_ofReal (affineBrownianRegulator_nonneg x hσ L (b.val : ℤ) T ω)]

theorem reflectedAtomicWeightedBoundary_bounds_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ b : Fin 2, ∀ T : ℝ≥0,
      0 ≤ reflectedAtomicWeightedBoundary L hL D hD x a κ b T ω ∧
        reflectedAtomicWeightedBoundary L hL D hD x a κ b T ω ≤
          affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ) T ω := by
  filter_upwards [affineBrownianLatticeRegular_ae x (Real.sqrt (2 * D)) L,
    reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω hp
  exact fun b T => reflectedAtomicWeightedBoundary_bounds L hL D hD x a κ hκ b hω hp.2.2.2.1 T

theorem reflectedAtomicWeightedBoundary_aestronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (b : Fin 2) (T : ℝ≥0) :
    AEStronglyMeasurable (reflectedAtomicWeightedBoundary L hL D hD x a κ b T)
      brownianDyadicMeasure := by
  let V : (ℕ → ℝ) → ℝ := fun ω =>
    limUnder atTop (fun n => reflectedAtomicWeightedBoundarySum L D x a κ b T n ω)
  refine ⟨V, ?_, ?_⟩
  · exact StronglyMeasurable.limUnder (fun n =>
      (reflectedAtomicWeightedBoundarySum_measurable L D x a κ b T n).stronglyMeasurable)
  · filter_upwards [reflectedAtomicWeightedBoundarySum_tendsto_ae L hL D hD x a κ hκ] with ω hω
    exact (hω b T).limUnder_eq.symm

theorem reflectedAtomicWeightedBoundary_memLp
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (b : Fin 2) (T : ℝ≥0) :
    MemLp (reflectedAtomicWeightedBoundary L hL D hD x a κ b T) 2 brownianDyadicMeasure := by
  have hK : MemLp (affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ) T)
      2 brownianDyadicMeasure := by
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl
    · exact reflectedLowerRegulator_memLp L hL D hD x T
    · exact reflectedUpperRegulator_memLp L hL D hD x T
  apply hK.mono' (reflectedAtomicWeightedBoundary_aestronglyMeasurable L hL D hD x a κ hκ b T)
  filter_upwards [reflectedAtomicWeightedBoundary_bounds_ae L hL D hD x a κ hκ] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hω b T).1] using (hω b T).2

end TimeTraps.Probability
