module

public import TimeTraps.Probability.MarkovFiniteKernelData

@[expose] public section

/-! Genuine finite-trajectory marginals. Removing the first observed
state integrates out the first transition; adjacent elapsed times merge
by the proved transition semigroup law. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]
variable (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)]

theorem finiteMarkovKernel_head (t : ℝ≥0) (d : List ℝ≥0) :
    (finiteMarkovKernel K (t :: d)).map (fun q => q 0) = K t := by
  have hm := (Kernel.map_comp_right
    ((Kernel.id ×ₖ finiteMarkovKernel K d) ∘ₖ K t)
    (finiteStateCons_measurable (α := α) d.length) (measurable_pi_apply 0)).symm
  change ((finiteMarkovKernel K (t :: d)).map (fun q => q 0)) = _ at hm
  rw [hm]
  have he : (fun q : Fin (d.length + 1) → α => q 0) ∘
      (fun p : α × (Fin d.length → α) => Fin.cons p.1 p.2) = Prod.fst := by
    funext p
    exact Fin.cons_zero _ _
  rw [he]
  rw [← Kernel.fst_eq, Kernel.fst_comp, Kernel.fst_prod, Kernel.id_comp]

theorem finiteMarkovKernel_tail (t : ℝ≥0) (d : List ℝ≥0) :
    (finiteMarkovKernel K (t :: d)).map Fin.tail = finiteMarkovKernel K d ∘ₖ K t := by
  rw [finiteMarkovKernel, ← Kernel.map_comp_right _
    (finiteStateCons_measurable d.length) (finiteStateTail_measurable d.length)]
  have he : (Fin.tail : (Fin (d.length + 1) → α) → (Fin d.length → α)) ∘
      (fun p : α × (Fin d.length → α) => Fin.cons p.1 p.2) = Prod.snd := by
    funext p
    exact Fin.tail_cons _ _
  rw [he]
  rw [← Kernel.snd_eq, Kernel.snd_comp, Kernel.snd_prod]

theorem finiteMarkovKernel_merge_first
    (hadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (s t : ℝ≥0) (d : List ℝ≥0) :
    (finiteMarkovKernel K (s :: t :: d)).map Fin.tail =
      finiteMarkovKernel K ((s + t) :: d) := by
  rw [finiteMarkovKernel_tail, finiteMarkovKernel, finiteMarkovKernel,
    ← Kernel.map_comp, Kernel.comp_assoc, ← hadd s t]

end TimeTraps.Probability
