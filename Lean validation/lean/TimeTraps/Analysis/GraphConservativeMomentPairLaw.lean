module

public import TimeTraps.Analysis.GraphConservativeMomentPairIndex

@[expose] public section

/-! The true two-time marginal of the chronological finite observation
law is the original earlier transition followed by the elapsed-time
transition. No graph Markov-process assumption is introduced. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem markovObservationFamily_pair_lintegral (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) {s t : ℝ≥0} (hst : s < t)
    {F : α × α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F (q ⟨s, by simp⟩, q ⟨t, by simp⟩) ∂markovObservationFamily K x {s, t}) =
      ∫⁻ y, ∫⁻ z, F (y, z) ∂K (t - s) y ∂K s x := by
  let I : Finset ℝ≥0 := {s, t}
  let H : (I → α) → ℝ≥0∞ := fun q => F (q ⟨s, by simp [I]⟩, q ⟨t, by simp [I]⟩)
  have hH : Measurable H := hF.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hm := Kernel.lintegral_map (finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·))))
    (observationState_measurable I) x hH
  change (∫⁻ q, H q ∂markovObservationFamily K x I) = _ at hm
  calc
    _ = ∫⁻ q, F (observationState {s, t} q ⟨s, by simp⟩,
        observationState {s, t} q ⟨t, by simp⟩)
          ∂finiteMarkovKernel K (observationDurations 0 (({s, t} : Finset ℝ≥0).sort (· ≤ ·))) x := hm
    _ = ∫⁻ q, F (q (observationPairIndex hst 0), q (observationPairIndex hst 1))
          ∂finiteMarkovKernel K (observationDurations 0 (({s, t} : Finset ℝ≥0).sort (· ≤ ·))) x :=
      lintegral_congr (fun q => congrArg F (observationState_pair hst q))
    _ = _ := finiteMarkovKernel_pair_lintegral_cast K s (t - s) x (observationPair_durations hst) hF

theorem markovObservationFamily_pair_map (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) {s t : ℝ≥0} (hst : s < t) :
    (markovObservationFamily K x {s, t}).map (fun q => (q ⟨s, by simp⟩, q ⟨t, by simp⟩)) =
      (K s x) ⊗ₘ K (t - s) := by
  apply Measure.ext_of_lintegral
  intro F hF
  calc
    _ = ∫⁻ q, F (q ⟨s, by simp⟩, q ⟨t, by simp⟩) ∂markovObservationFamily K x {s, t} :=
      lintegral_map hF ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
    _ = ∫⁻ y, ∫⁻ z, F (y, z) ∂K (t - s) y ∂K s x :=
      markovObservationFamily_pair_lintegral K x hst hF
    _ = _ := (Measure.lintegral_compProd hF).symm

end TimeTraps.Probability
