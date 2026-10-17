module

public import TimeTraps.Probability.ReflectedAtomicHazardStieltjesIntegral
public import TimeTraps.Probability.ReflectedInteriorOccupationMoments

@[expose] public section

/-! Actual survival-weighted occupation integrals and literal measurable
dyadic sums. Pathwise convergence is proved from the actual continuous
survival weight and Stieltjes occupation increments, on the finite-label
regular event. No measurability of a random-measure map is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

def reflectedAtomicWeightedOccupation (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (i : ι) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
    ∂reflectedInteriorOccupationTimeMeasure x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω

def reflectedAtomicWeightedOccupationSum (L D x : ℝ) (a κ : ι → ℝ)
    (i : ι) (T : ℝ≥0) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (2 ^ n),
    (reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i)
      (brownianDyadicGrid T n j.succ) ω -
    reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i)
      (brownianDyadicGrid T n j.castSucc) ω) *
    reflectedAtomicSurvival L D x a κ (brownianDyadicGrid T n j.castSucc) ω

theorem reflectedAtomicWeightedOccupationSum_measurable (L D x : ℝ) (a κ : ι → ℝ)
    (i : ι) (T : ℝ≥0) (n : ℕ) :
    Measurable (reflectedAtomicWeightedOccupationSum L D x a κ i T n) := by
  have hφ (t : ℝ≥0) : Measurable (fun ω : ℕ → ℝ => (t, ω)) := measurable_const.prodMk measurable_id
  have he (t : ℝ≥0) := (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable
    x (Real.sqrt (2 * D)) L (a i)).comp (hφ t)
  have hw (t : ℝ≥0) := (reflectedAtomicSurvival_jointlyMeasurable L D x a κ).comp (hφ t)
  unfold reflectedAtomicWeightedOccupationSum
  exact Finset.measurable_sum Finset.univ (fun (j : Fin (2 ^ n)) _ =>
    ((he (brownianDyadicGrid T n j.succ)).sub
      (he (brownianDyadicGrid T n j.castSucc))).mul (hw (brownianDyadicGrid T n j.castSucc)))

theorem reflectedAtomicWeightedOccupationSum_eq_stieltjes
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (i : ι) {ω : ℕ → ℝ}
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω)
    (T : ℝ≥0) (n : ℕ) :
    reflectedAtomicWeightedOccupationSum L D x a κ i T n ω =
      dyadicStieltjesSum (reflectedInteriorOccupationStieltjes x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω)
        (fun t => reflectedAtomicSurvival L D x a κ t ω) T n := by
  unfold reflectedAtomicWeightedOccupationSum dyadicStieltjesSum
  apply Finset.sum_congr rfl
  intro j _
  rw [reflectedInteriorOccupationStieltjes_apply_nnreal _ hL hω,
    reflectedInteriorOccupationStieltjes_apply_nnreal _ hL hω]

theorem reflectedAtomicWeightedOccupationSum_tendsto_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι, ∀ T : ℝ≥0,
      Tendsto (fun n => reflectedAtomicWeightedOccupationSum L D x a κ i T n ω) atTop
        (𝓝 (reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω)) := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [hall, reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω hp
  intro i T
  have hd := dyadicStieltjesSum_tendsto (reflectedInteriorOccupationStieltjes x
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω)
    (fun t => reflectedAtomicSurvival L D x a κ t ω) hp.2.2.2.1 T
  rw [← reflectedInteriorOccupationTimeMeasure_eq_stieltjes] at hd
  exact hd.congr' (Eventually.of_forall (fun n =>
    (reflectedAtomicWeightedOccupationSum_eq_stieltjes L hL D hD x a κ i (hω i) T n).symm))

end TimeTraps.Probability

end
