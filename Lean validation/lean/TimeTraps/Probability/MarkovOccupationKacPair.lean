module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! The signed two-test occupation pairing derived from an explicit
chronological two-time law. No conditional Markov property is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [TopologicalSpace α] [BorelSpace α] [SecondCountableTopology α] [CompactSpace α]

noncomputable def markovOccupationPair (K : ℝ≥0 → Kernel α α) (x : α)
    (f g : C(α, ℝ)) (s t : ℝ≥0) : ℝ :=
  ∫ y, f y * (∫ z, g z ∂K (t - s) y) ∂K s x

theorem markovOccupationPair_integrable (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (f g : C(α, ℝ)) (s t : ℝ≥0) :
    Integrable (fun p : α × α => f p.1 * g p.2) ((K s x) ⊗ₘ K (t - s)) :=
  ((f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem markovOccupationPair_eq_productIntegral (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (f g : C(α, ℝ)) (s t : ℝ≥0) :
    (∫ p : α × α, f p.1 * g p.2 ∂((K s x) ⊗ₘ K (t - s))) =
      markovOccupationPair K x f g s t := by
  rw [Measure.integral_compProd (markovOccupationPair_integrable K x f g s t)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun y =>
    integral_const_mul (f y) (fun z => g z)))

theorem markovOccupationPair_expectation (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω)
    (X : ℝ≥0 → Ω → α) {s t : ℝ≥0}
    (hs : Measurable (X s)) (ht : Measurable (X t))
    (hPair : μ.map (fun ω => (X s ω, X t ω)) = (K s x) ⊗ₘ K (t - s))
    (f g : C(α, ℝ)) :
    Integrable (fun ω => f (X s ω) * g (X t ω)) μ ∧
      (∫ ω, f (X s ω) * g (X t ω) ∂μ) = markovOccupationPair K x f g s t := by
  have hm : MeasurePreserving (fun ω => (X s ω, X t ω)) μ ((K s x) ⊗ₘ K (t - s)) :=
    ⟨hs.prodMk ht, hPair⟩
  refine ⟨hm.integrable_comp_of_integrable (markovOccupationPair_integrable K x f g s t), ?_⟩
  have hfg : Continuous (fun p : α × α => f p.1 * g p.2) :=
    (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)
  calc
    _ = ∫ p : α × α, f p.1 * g p.2 ∂μ.map (fun ω => (X s ω, X t ω)) :=
      (integral_map (hs.prodMk ht).aemeasurable hfg.aestronglyMeasurable).symm
    _ = ∫ p : α × α, f p.1 * g p.2 ∂((K s x) ⊗ₘ K (t - s)) :=
      congrArg (fun ν => ∫ p : α × α, f p.1 * g p.2 ∂ν) hPair
    _ = _ := markovOccupationPair_eq_productIntegral K x f g s t

end TimeTraps.Probability
