module

public import TimeTraps.Probability.MarkovObservationAppendIntegral
public import TimeTraps.Probability.MarkovObservationExtract

@[expose] public section

/-! The actual finite history and one future observation have the
composition-product law with the transition from the last past state. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem markovObservationFamily_append_lintegral (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (I : Finset ℝ≥0) {s t : ℝ≥0}
    (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) (hst : s < t)
    {F : (I → α) × α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F (observationExtract I t q) ∂markovObservationFamily K x (insert t I)) =
      ∫⁻ q, ∫⁻ y, F (q, y) ∂K (t - s) (q ⟨s, hs⟩) ∂markovObservationFamily K x I := by
  let κ : Kernel (I → α) α := (K (t - s)).comap (fun q => q ⟨s, hs⟩) (measurable_pi_apply _)
  have hH : Measurable (fun q : I → α => ∫⁻ y, F (q, y) ∂K (t - s) (q ⟨s, hs⟩)) :=
    hF.lintegral_kernel_prod_right' (κ := κ)
  calc
    _ = ∫⁻ q, F (observationExtract I t (observationState (insert t I) q))
        ∂finiteMarkovKernel K (observationDurations 0 ((insert t I).sort (· ≤ ·))) x :=
      markovObservationFamily_lintegral K x (insert t I) (hF.comp (observationExtract_measurable I t))
    _ = ∫⁻ q, ∫⁻ y, F (observationExtract I t (observationState (insert t I)
        (observationTupleSnoc I t (fun u hu => (hmax u hu).trans_lt hst) q y)))
        ∂K (t - s) (observationState I q ⟨s, hs⟩)
        ∂finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·))) x :=
      observation_lintegral_append K x I hs hmax hst
        ((hF.comp (observationExtract_measurable I t)).comp (observationState_measurable (insert t I)))
    _ = ∫⁻ q, ∫⁻ y, F (observationState I q, y)
        ∂K (t - s) (observationState I q ⟨s, hs⟩)
        ∂finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·))) x := by
      simp only [observationExtract_snoc]
    _ = _ := (markovObservationFamily_lintegral K x I hH).symm

theorem markovObservationFamily_append_law (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (I : Finset ℝ≥0) {s t : ℝ≥0}
    (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) (hst : s < t) :
    (markovObservationFamily K x (insert t I)).map (observationExtract I t) =
      (markovObservationFamily K x I) ⊗ₘ
        (K (t - s)).comap (fun q => q ⟨s, hs⟩) (measurable_pi_apply _) := by
  let inst := markovObservationFamily_probability K x I
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (observationExtract_measurable I t), Measure.lintegral_compProd hF]
  exact markovObservationFamily_append_lintegral K x I hs hmax hst hF

end TimeTraps.Probability
