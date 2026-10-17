module

public import Mathlib.Probability.Martingale.Basic
public import TimeTraps.Probability.DyadicStieltjesRightIntegral

@[expose] public section

/-! Bounded predictable weights preserve the zero expectation of actual
martingale increments. The finite dyadic sums will be passed to their
pathwise Stieltjes limit using an integrable compact-path bound. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {M H : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem martingale_bounded_increment_integrable
    (hM : Martingale M 𝓕 μ) (hH : StronglyAdapted 𝓕 H)
    {C : ℝ} (hb : ∀ t ω, ‖H t ω‖ ≤ C) (s t : ℝ≥0) :
    Integrable (fun ω => H s ω * (M t ω - M s ω)) μ :=
  ((hM.integrable t).sub (hM.integrable s)).bdd_mul
    ((hH s).mono (𝓕.le s)).aestronglyMeasurable (Eventually.of_forall (hb s))

theorem martingale_bounded_increment_mean [IsFiniteMeasure μ]
    (hM : Martingale M 𝓕 μ) (hH : StronglyAdapted 𝓕 H)
    {C : ℝ} (hb : ∀ t ω, ‖H t ω‖ ≤ C) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, H s ω * (M t ω - M s ω) ∂μ) = 0 := by
  have hi := martingale_bounded_increment_integrable hM hH hb s t
  have hd := (hM.integrable t).sub (hM.integrable s)
  have hsub : M t - M s = (fun ω => M t ω - M s ω) := rfl
  have hmul : H s * (fun ω => M t ω - M s ω) =
      (fun ω => H s ω * (M t ω - M s ω)) := rfl
  have hc : μ[(fun ω => M t ω - M s ω) | 𝓕 s] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [condExp_sub (hM.integrable t) (hM.integrable s) (𝓕 s),
      hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω he ht hs
    simpa only [Pi.sub_apply, ht, hs, sub_self, hsub] using he
  have he : μ[(fun ω => H s ω * (M t ω - M s ω)) | 𝓕 s] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [condExp_mul_of_aestronglyMeasurable_left (hH s).aestronglyMeasurable hi hd,
      hc] with ω hp hz
    simpa only [Pi.mul_apply, hz, mul_zero, hmul] using hp
  calc
    _ = ∫ ω, (μ[(fun ω => H s ω * (M t ω - M s ω)) | 𝓕 s]) ω ∂μ :=
      (integral_condExp (𝓕.le s)).symm
    _ = ∫ _ω, (0 : ℝ) ∂μ := integral_congr_ae he
    _ = 0 := integral_zero _ _

noncomputable def martingaleDyadicWeightedSum (M H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (2 ^ n), H (brownianDyadicGrid T n i.castSucc) ω *
    (M (brownianDyadicGrid T n i.succ) ω - M (brownianDyadicGrid T n i.castSucc) ω)

theorem martingaleDyadicWeightedSum_integrable
    (hM : Martingale M 𝓕 μ) (hH : StronglyAdapted 𝓕 H)
    {C : ℝ} (hb : ∀ t ω, ‖H t ω‖ ≤ C) (T : ℝ≥0) (n : ℕ) :
    Integrable (martingaleDyadicWeightedSum M H T n) μ :=
  integrable_finsetSum _ (fun _ _ => martingale_bounded_increment_integrable hM hH hb _ _)

theorem martingaleDyadicWeightedSum_mean [IsFiniteMeasure μ]
    (hM : Martingale M 𝓕 μ) (hH : StronglyAdapted 𝓕 H)
    {C : ℝ} (hb : ∀ t ω, ‖H t ω‖ ≤ C) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, martingaleDyadicWeightedSum M H T n ω ∂μ) = 0 := by
  unfold martingaleDyadicWeightedSum
  rw [integral_finsetSum _ (fun _ _ => martingale_bounded_increment_integrable hM hH hb _ _)]
  have hz (i : Fin (2 ^ n)) : (∫ ω, H (brownianDyadicGrid T n i.castSucc) ω *
      (M (brownianDyadicGrid T n i.succ) ω - M (brownianDyadicGrid T n i.castSucc) ω) ∂μ) = 0 :=
    martingale_bounded_increment_mean hM hH hb (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i))
  simp only [hz, Finset.sum_const_zero]

end TimeTraps.Probability
