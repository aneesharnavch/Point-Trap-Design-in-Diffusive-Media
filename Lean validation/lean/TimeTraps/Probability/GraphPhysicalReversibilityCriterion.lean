module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd

@[expose] public section

/-! Continuous-product pairings determine the full joint transition
measure. Symmetry of those pairings therefore implies literal detailed
balance on every measurable pair of sets, not only continuous tests. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ENNReal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [HasOuterApproxClosed X]

omit [HasOuterApproxClosed X] in
theorem kernel_compProd_integral_product (K : Kernel X X) [IsMarkovKernel K]
    (μ : Measure X) [IsFiniteMeasure μ] (f g : X →ᵇ ℝ) :
    (∫ p, f p.1 * g p.2 ∂(μ ⊗ₘ K)) =
      ∫ x, f x * (∫ y, g y ∂K x) ∂μ := by
  have hm : Measurable (fun p : X × X => f p.1 * g p.2) :=
    (f.continuous.measurable.comp measurable_fst).mul
      (g.continuous.measurable.comp measurable_snd)
  have hi : Integrable (fun p : X × X => f p.1 * g p.2) (μ ⊗ₘ K) := by
    apply (integrable_const (‖f‖ * ‖g‖)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (f.norm_coe_le_norm p.1) (g.norm_coe_le_norm p.2)
        (norm_nonneg _) (norm_nonneg _))
  rw [Measure.integral_compProd hi]
  exact integral_congr_ae (Eventually.of_forall (fun x => by
    dsimp only
    exact integral_const_mul _ _))

theorem kernel_compProd_swap_of_pairings (K : Kernel X X) [IsMarkovKernel K]
    (μ : Measure X) [IsFiniteMeasure μ]
    (hs : ∀ f g : X →ᵇ ℝ,
      (∫ x, f x * (∫ y, g y ∂K x) ∂μ) = ∫ x, g x * (∫ y, f y ∂K x) ∂μ) :
    (μ ⊗ₘ K).map Prod.swap = μ ⊗ₘ K := by
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  have hm : Measurable (fun p : X × X => f p.1 * g p.2) :=
    (f.continuous.measurable.comp measurable_fst).mul
      (g.continuous.measurable.comp measurable_snd)
  rw [integral_map measurable_swap.aemeasurable hm.aestronglyMeasurable]
  calc
    _ = ∫ p, g p.1 * f p.2 ∂(μ ⊗ₘ K) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => mul_comm _ _)
    _ = ∫ x, g x * (∫ y, f y ∂K x) ∂μ := kernel_compProd_integral_product K μ g f
    _ = ∫ x, f x * (∫ y, g y ∂K x) ∂μ := (hs f g).symm
    _ = _ := (kernel_compProd_integral_product K μ f g).symm

theorem kernel_reversible_of_pairings (K : Kernel X X) [IsMarkovKernel K]
    (μ : Measure X) [IsFiniteMeasure μ]
    (hs : ∀ f g : X →ᵇ ℝ,
      (∫ x, f x * (∫ y, g y ∂K x) ∂μ) = ∫ x, g x * (∫ y, f y ∂K x) ∂μ) :
    K.IsReversible μ := by
  intro A B hA hB
  have he := congrArg (fun ν : Measure (X × X) => ν (A ×ˢ B))
    (kernel_compProd_swap_of_pairings K μ hs)
  rw [Measure.map_apply measurable_swap (hA.prod hB), preimage_swap_prod,
    Measure.compProd_apply_prod hB hA, Measure.compProd_apply_prod hA hB] at he
  exact he.symm

end TimeTraps.Probability
