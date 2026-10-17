module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! A genuine composition-product joint law gives the conditional
set-integral identity for every bounded signed Borel observation. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

theorem kernel_integral_bound (κ : Kernel α β) [IsMarkovKernel κ]
    (f : β → ℝ) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) (a : α) :
    ‖∫ z, f z ∂κ a‖ ≤ C := by
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ a) (Eventually.of_forall hC)

theorem kernel_pair_bounded_setIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (hY : Measurable Y) (hZ : Measurable Z)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hlaw : μ.map (fun ω => (Y ω, Z ω)) = (μ.map Y) ⊗ₘ κ)
    (f : β → ℝ) (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C)
    {S : Set α} (hS : MeasurableSet S) :
    (∫ ω in Y ⁻¹' S, f (Z ω) ∂μ) =
      ∫ ω in Y ⁻¹' S, (∫ z, f z ∂κ (Y ω)) ∂μ := by
  let F : α × β → ℝ := (Prod.fst ⁻¹' S).indicator (fun p => f p.2)
  have hF : Measurable F := (hf.comp measurable_snd).indicator (hS.preimage measurable_fst)
  have hb (p : α × β) : ‖F p‖ ≤ C := by
    by_cases hp : p.1 ∈ S
    · simpa [F, hp] using hC p.2
    · simpa [F, hp] using hC0
  have hi : Integrable F ((μ.map Y) ⊗ₘ κ) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hb)
  let H : α → ℝ := S.indicator (fun a => ∫ z, f z ∂κ a)
  have hH : Measurable H := hf.stronglyMeasurable.integral_kernel.measurable.indicator hS
  have hsec (a : α) : (∫ z, F (a, z) ∂κ a) = H a := by
    by_cases ha : a ∈ S <;> simp [F, H, ha]
  calc
    _ = ∫ ω, F (Y ω, Z ω) ∂μ := by
      rw [← integral_indicator (hY hS)]
      rfl
    _ = ∫ p, F p ∂μ.map (fun ω => (Y ω, Z ω)) :=
      (integral_map (hY.prodMk hZ).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂(μ.map Y) ⊗ₘ κ := by rw [hlaw]
    _ = ∫ a, ∫ z, F (a, z) ∂κ a ∂μ.map Y := Measure.integral_compProd hi
    _ = ∫ a, H a ∂μ.map Y := integral_congr_ae (Eventually.of_forall hsec)
    _ = ∫ ω, H (Y ω) ∂μ := integral_map hY.aemeasurable hH.aestronglyMeasurable
    _ = _ := by
      rw [← integral_indicator (hY hS)]
      rfl

end TimeTraps.Probability
