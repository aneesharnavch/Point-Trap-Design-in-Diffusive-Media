module

public import TimeTraps.Probability.ReflectedAtomicWeightedOccupationData

@[expose] public section

/-! Actual survival-weighted lower and upper regulator integrals.
Their literal dyadic sums involve only measurable actual regulator and
survival values. The finite-label and lattice events give convergence
simultaneously at every finite horizon for both boundary indices. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

def reflectedAtomicWeightedBoundary (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (b : Fin 2) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω
    ∂affineBrownianRegulatorTimeMeasure x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (b.val : ℤ) ω

def reflectedAtomicWeightedBoundarySum (L D x : ℝ) (a κ : ι → ℝ)
    (b : Fin 2) (T : ℝ≥0) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (2 ^ n),
    (affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ)
      (brownianDyadicGrid T n j.succ) ω -
    affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ)
      (brownianDyadicGrid T n j.castSucc) ω) *
    reflectedAtomicSurvival L D x a κ (brownianDyadicGrid T n j.castSucc) ω

theorem reflectedAtomicWeightedBoundarySum_measurable (L D x : ℝ) (a κ : ι → ℝ)
    (b : Fin 2) (T : ℝ≥0) (n : ℕ) :
    Measurable (reflectedAtomicWeightedBoundarySum L D x a κ b T n) := by
  have hφ (t : ℝ≥0) : Measurable (fun ω : ℕ → ℝ => (t, ω)) := measurable_const.prodMk measurable_id
  have he (t : ℝ≥0) := (affineBrownianRegulator_time_jointlyMeasurable
    x (Real.sqrt (2 * D)) L (b.val : ℤ)).comp (hφ t)
  have hw (t : ℝ≥0) := (reflectedAtomicSurvival_jointlyMeasurable L D x a κ).comp (hφ t)
  unfold reflectedAtomicWeightedBoundarySum
  exact Finset.measurable_sum Finset.univ (fun (j : Fin (2 ^ n)) _ =>
    ((he (brownianDyadicGrid T n j.succ)).sub
      (he (brownianDyadicGrid T n j.castSucc))).mul (hw (brownianDyadicGrid T n j.castSucc)))

theorem reflectedAtomicWeightedBoundarySum_eq_stieltjes
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (b : Fin 2) {ω : ℕ → ℝ}
    (hω : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω)
    (T : ℝ≥0) (n : ℕ) :
    reflectedAtomicWeightedBoundarySum L D x a κ b T n ω =
      dyadicStieltjesSum (affineBrownianRegulatorStieltjes x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (b.val : ℤ) ω)
        (fun t => reflectedAtomicSurvival L D x a κ t ω) T n := by
  unfold reflectedAtomicWeightedBoundarySum dyadicStieltjesSum
  apply Finset.sum_congr rfl
  intro j _
  rw [affineBrownianRegulatorStieltjes_apply _ hL hω,
    affineBrownianRegulatorStieltjes_apply _ hL hω]
  apply congrArg (fun z : ℝ => z * reflectedAtomicSurvival L D x a κ (brownianDyadicGrid T n j.castSucc) ω)
  exact congrArg₂ (fun s t : ℝ≥0 =>
    affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ) s ω -
      affineBrownianRegulator x (Real.sqrt (2 * D)) L (b.val : ℤ) t ω)
    (Real.toNNReal_coe (r := brownianDyadicGrid T n j.succ)).symm
    (Real.toNNReal_coe (r := brownianDyadicGrid T n j.castSucc)).symm

theorem reflectedAtomicWeightedBoundarySum_tendsto_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ b : Fin 2, ∀ T : ℝ≥0,
      Tendsto (fun n => reflectedAtomicWeightedBoundarySum L D x a κ b T n ω) atTop
        (𝓝 (reflectedAtomicWeightedBoundary L hL D hD x a κ b T ω)) := by
  filter_upwards [affineBrownianLatticeRegular_ae x (Real.sqrt (2 * D)) L,
    reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hω hp
  intro b T
  have hd := dyadicStieltjesSum_tendsto (affineBrownianRegulatorStieltjes x
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (b.val : ℤ) ω)
    (fun t => reflectedAtomicSurvival L D x a κ t ω) hp.2.2.2.1 T
  exact hd.congr' (Eventually.of_forall (fun n =>
    (reflectedAtomicWeightedBoundarySum_eq_stieltjes L hL D hD x a κ b hω T n).symm))

end TimeTraps.Probability

end
