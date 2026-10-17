module

public import TimeTraps.Probability.MarkovOccupationKacPair
public import TimeTraps.Probability.OccupationProductTime
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

/-! Measurable finite-time occupation integrands and valid chronological
replacement on the Lebesgue time square. Kernel time measurability is
obtained where needed from the genuine process pairing. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [TopologicalSpace α] [BorelSpace α] [SecondCountableTopology α] [CompactSpace α]

omit [SecondCountableTopology α] [CompactSpace α] in
theorem occupationObservation_measurable (X : ℝ≥0 → Ω → α)
    (hX : Measurable (Function.uncurry X)) (f : C(α, ℝ)) :
    Measurable (fun p : ℝ × Ω => f (X p.1.toNNReal p.2)) :=
  f.continuous.measurable.comp
    (hX.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd))

theorem markovOccupationPair_expectation_real (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω) (X : ℝ≥0 → Ω → α)
    (hX : Measurable (Function.uncurry X))
    (hPair : ∀ s t : ℝ≥0, s < t → μ.map (fun ω => (X s ω, X t ω)) =
      (K s x) ⊗ₘ K (t - s)) (f g : C(α, ℝ)) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∫ ω, f (X s.toNNReal ω) * g (X t.toNNReal ω) ∂μ) =
      markovOccupationPair K x f g s.toNNReal t.toNNReal := by
  exact (markovOccupationPair_expectation K x μ X
    (hX.comp (measurable_const.prodMk measurable_id))
    (hX.comp (measurable_const.prodMk measurable_id))
    (hPair _ _ ((Real.toNNReal_lt_toNNReal_iff_of_nonneg hs).mpr hst)) f g).2

theorem markovOccupationPair_ordered_replacement (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → α) (hX : Measurable (Function.uncurry X))
    (hPair : ∀ s t : ℝ≥0, s < t → μ.map (fun ω => (X s ω, X t ω)) =
      (K s x) ⊗ₘ K (t - s)) (f g : C(α, ℝ)) (T : ℝ) :
    Integrable (fun p : ℝ × ℝ => if p.1 < p.2 then
      markovOccupationPair K x f g p.1.toNNReal p.2.toNNReal else 0)
        ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))) ∧
    orderedTimeIntegral (volume.restrict (Ioc 0 T))
      (fun p => ∫ ω, f (X p.1.toNNReal ω) * g (X p.2.toNNReal ω) ∂μ) =
    orderedTimeIntegral (volume.restrict (Ioc 0 T))
      (fun p => markovOccupationPair K x f g p.1.toNNReal p.2.toNNReal) := by
  let H : ℝ × ℝ → ℝ := fun p => ∫ ω, f (X p.1.toNNReal ω) * g (X p.2.toNNReal ω) ∂μ
  let J : ℝ × ℝ → ℝ := fun p => markovOccupationPair K x f g p.1.toNNReal p.2.toNNReal
  have hi : Integrable H ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))) :=
    occupationProduct_mean_integrable μ (volume.restrict (Ioc 0 T))
      (fun s ω => f (X s.toNNReal ω)) (fun t ω => g (X t.toNNReal ω))
      (occupationObservation_measurable X hX f) (occupationObservation_measurable X hX g)
      (fun _ _ => f.norm_coe_le_norm _) (fun _ _ => g.norm_coe_le_norm _)
  have he : ∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s < t → H (s, t) = J (s, t) := by
    intro s hs t _ht hst
    exact markovOccupationPair_expectation_real K x μ X hX hPair f g hs.1.le hst
  exact ⟨orderedTimeIntegrand_Ioc_integrable T H J hi he,
    integral_congr_ae (orderedTimeIntegrand_Ioc_congr T H J he)⟩

end TimeTraps.Probability
