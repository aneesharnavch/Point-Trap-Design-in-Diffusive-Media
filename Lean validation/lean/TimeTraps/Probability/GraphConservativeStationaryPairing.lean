module

public import TimeTraps.Probability.GraphConservativeReversibility
public import TimeTraps.Probability.GraphPhysicalReversibilityCriterion
public import TimeTraps.Analysis.GraphShiftedContactFellerOperator

@[expose] public section

/-! Reversibility of the actual reference transition gives symmetry of
continuous Feller pairings. The measure argument first proves equality
of the whole swapped joint measure on measurable rectangles. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem kernel_compProd_swap_of_reversible (K : Kernel X X) [IsMarkovKernel K]
    (μ : Measure X) [IsFiniteMeasure μ] (hK : K.IsReversible μ) :
    (μ ⊗ₘ K).map Prod.swap = μ ⊗ₘ K := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB), preimage_swap_prod,
    Measure.compProd_apply_prod hB hA, Measure.compProd_apply_prod hA hB]
  exact hK hB hA

variable [TopologicalSpace X] [BorelSpace X]

theorem kernel_pairing_of_reversible (K : Kernel X X) [IsMarkovKernel K]
    (μ : Measure X) [IsFiniteMeasure μ] (hK : K.IsReversible μ) (f g : X →ᵇ ℝ) :
    (∫ x, f x * (∫ y, g y ∂K x) ∂μ) =
      ∫ x, g x * (∫ y, f y ∂K x) ∂μ := by
  have hm : Measurable (fun p : X × X => f p.1 * g p.2) :=
    (f.continuous.measurable.comp measurable_fst).mul
      (g.continuous.measurable.comp measurable_snd)
  have he := integral_map (μ := μ ⊗ₘ K) measurable_swap.aemeasurable hm.aestronglyMeasurable
  rw [kernel_compProd_swap_of_reversible K μ hK] at he
  calc
    _ = ∫ p, f p.1 * g p.2 ∂(μ ⊗ₘ K) := (kernel_compProd_integral_product K μ f g).symm
    _ = ∫ p, f p.2 * g p.1 ∂(μ ⊗ₘ K) := he
    _ = ∫ p, g p.1 * f p.2 ∂(μ ⊗ₘ K) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => mul_comm _ _)
    _ = _ := kernel_compProd_integral_product K μ g f

end TimeTraps.Probability

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedFeller_length_pairing
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (f g : C(GraphRealization P.geometry, ℝ)) :
    (∫ x, f x * P.realizedFeller t g x ∂P.geometry.lengthMeasure) =
      ∫ x, g x * P.realizedFeller t f x ∂P.geometry.lengthMeasure := by
  let inst := P.realizedTransition_isMarkov h0 t
  have he := kernel_pairing_of_reversible (P.realizedTransition t) P.geometry.lengthMeasure
    (P.realizedTransition_reversible t) (BoundedContinuousFunction.mkOfCompact f)
    (BoundedContinuousFunction.mkOfCompact g)
  change (∫ x, f x * (∫ y, g y ∂P.realizedTransition t x) ∂P.geometry.lengthMeasure) =
    ∫ x, g x * (∫ y, f y ∂P.realizedTransition t x) ∂P.geometry.lengthMeasure at he
  simpa only [P.realizedFeller_apply] using he

end TimeTraps.Analysis
