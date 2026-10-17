module

public import TimeTraps.Probability.MartingaleBoundedIncrement
public import TimeTraps.Probability.StieltjesWeightedIncrementBound

@[expose] public section

/-! The actual survival-weighted martingale product has expectation zero.
Predictable finite sums have zero means; the exact pathwise product and
an integrable compact bound justify their limit. The increasing weight
loss is only required to agree with the adapted weight almost surely. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {M H : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

noncomputable def martingaleStieltjesProduct (M H : ℝ≥0 → Ω → ℝ)
    (K : Ω → StieltjesFunction ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  (H T ω * M T ω - H 0 ω * M 0 ω) +
    ∫ r in Ioc (0 : ℝ) (T : ℝ), M r.toNNReal ω ∂(K ω).measure

theorem martingaleDyadicWeightedSum_stieltjes_tendsto
    (K : Ω → StieltjesFunction ℝ) (T : ℝ≥0)
    (hM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hHK : ∀ᵐ ω ∂μ, ∀ t, H t ω = 1 - K ω (t : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => martingaleDyadicWeightedSum M H T n ω) atTop
      (𝓝 (martingaleStieltjesProduct M H K T ω)) := by
  filter_upwards [hM, hHK] with ω hm hk
  have he (n : ℕ) : martingaleDyadicWeightedSum M H T n ω =
      dyadicWeightedIncrement (fun t => 1 - K ω (t : ℝ)) (fun t => M t ω) T n := by
    simp only [martingaleDyadicWeightedSum, dyadicWeightedIncrement, hk]
  have hz : ((0 : ℝ≥0) : ℝ) = 0 := rfl
  simpa only [he, martingaleStieltjesProduct, hk, hz] using
    dyadicWeightedIncrement_loss_tendsto (K ω) (fun t => M t ω) hm T

theorem martingaleDyadicWeightedSum_stieltjes_bound
    (K : Ω → StieltjesFunction ℝ) (T : ℝ≥0) (B : Ω → ℝ)
    (hHK : ∀ᵐ ω ∂μ, ∀ t, H t ω = 1 - K ω (t : ℝ))
    (hK : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, 0 ≤ K ω (t : ℝ) ∧ K ω (t : ℝ) ≤ 1)
    (hMB : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |M t ω| ≤ B ω) :
    ∀ᵐ ω ∂μ, ∀ n, ‖martingaleDyadicWeightedSum M H T n ω‖ ≤ 3 * B ω := by
  filter_upwards [hHK, hK, hMB] with ω hk hb hm
  intro n
  have he : martingaleDyadicWeightedSum M H T n ω =
      dyadicWeightedIncrement (fun t => 1 - K ω (t : ℝ)) (fun t => M t ω) T n := by
    simp only [martingaleDyadicWeightedSum, dyadicWeightedIncrement, hk]
  rw [he, Real.norm_eq_abs]
  exact dyadicWeightedIncrement_loss_bound (K ω) (fun t => M t ω) T hb hm n

theorem martingaleStieltjesProduct_integrable_mean [IsFiniteMeasure μ]
    (hM : Martingale M 𝓕 μ) (hH : StronglyAdapted 𝓕 H)
    {C : ℝ} (hb : ∀ t ω, ‖H t ω‖ ≤ C)
    (K : Ω → StieltjesFunction ℝ) (T : ℝ≥0) (B : Ω → ℝ) (hB : Integrable B μ)
    (hMc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hHK : ∀ᵐ ω ∂μ, ∀ t, H t ω = 1 - K ω (t : ℝ))
    (hK : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, 0 ≤ K ω (t : ℝ) ∧ K ω (t : ℝ) ≤ 1)
    (hMB : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |M t ω| ≤ B ω) :
    Integrable (martingaleStieltjesProduct M H K T) μ ∧
      (∫ ω, martingaleStieltjesProduct M H K T ω ∂μ) = 0 := by
  have hm (n : ℕ) := (martingaleDyadicWeightedSum_integrable hM hH hb T n).aestronglyMeasurable
  have hp := martingaleDyadicWeightedSum_stieltjes_tendsto K T hMc hHK
  have hbound := martingaleDyadicWeightedSum_stieltjes_bound K T B hHK hK hMB
  have hlimbound : ∀ᵐ ω ∂μ, ‖martingaleStieltjesProduct M H K T ω‖ ≤ 3 * B ω := by
    filter_upwards [hp, hbound] with ω hω hωb
    exact le_of_tendsto hω.norm (Eventually.of_forall hωb)
  have hi : Integrable (martingaleStieltjesProduct M H K T) μ :=
    (hB.const_mul 3).mono' (aestronglyMeasurable_of_tendsto_ae atTop hm hp) hlimbound
  have hlim := tendsto_integral_of_dominated_convergence (fun ω => 3 * B ω) hm
    (hB.const_mul 3) (fun n => hbound.mono (fun _ hω => hω n)) hp
  have hzero (n : ℕ) : (∫ ω, martingaleDyadicWeightedSum M H T n ω ∂μ) = 0 :=
    martingaleDyadicWeightedSum_mean hM hH hb T n
  simp only [hzero] at hlim
  exact ⟨hi, (tendsto_nhds_unique tendsto_const_nhds hlim).symm⟩

end TimeTraps.Probability
