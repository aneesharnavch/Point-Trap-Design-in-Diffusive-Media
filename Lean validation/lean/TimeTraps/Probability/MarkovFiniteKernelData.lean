module

public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic

@[expose] public section

/-! Actual finite trajectory kernels obtained by iterating transition
kernels through an ordered list of elapsed times. The state tuple records
every visited state; probability normalization and the iterated integral
formula are derived from the given Markov transitions. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem finiteStateCons_measurable (n : ℕ) :
    Measurable (fun p : α × (Fin n → α) => (Fin.cons p.1 p.2 : Fin (n + 1) → α)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

theorem finiteStateTail_measurable (n : ℕ) :
    Measurable (Fin.tail : (Fin (n + 1) → α) → (Fin n → α)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.succ

noncomputable def finiteMarkovKernel (K : ℝ≥0 → Kernel α α) :
    (d : List ℝ≥0) → Kernel α (Fin d.length → α)
  | [] => Kernel.deterministic (fun _ => Fin.elim0) (measurable_const)
  | t :: d => ((Kernel.id ×ₖ finiteMarkovKernel K d) ∘ₖ K t).map
      (fun p : α × (Fin d.length → α) => Fin.cons p.1 p.2)

instance finiteMarkovKernel_markov (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (d : List ℝ≥0) : IsMarkovKernel (finiteMarkovKernel K d) := by
  induction d with
  | nil => unfold finiteMarkovKernel; infer_instance
  | cons t d ih =>
    let := ih
    rw [finiteMarkovKernel]
    exact Kernel.IsMarkovKernel.map _ (finiteStateCons_measurable d.length)

set_option backward.isDefEq.respectTransparency false in
theorem finiteMarkovKernel_lintegral_cons (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (t : ℝ≥0) (d : List ℝ≥0) (x : α)
    {F : (Fin (d.length + 1) → α) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂finiteMarkovKernel K (t :: d) x) =
      ∫⁻ y, ∫⁻ q, F (Fin.cons y q) ∂finiteMarkovKernel K d y ∂K t x := by
  have hm := Kernel.lintegral_map
    ((Kernel.id ×ₖ finiteMarkovKernel K d) ∘ₖ K t)
    (finiteStateCons_measurable (α := α) d.length) x hF
  change (∫⁻ p, F p ∂finiteMarkovKernel K (t :: d) x) = _ at hm
  rw [hm]
  have hc := Kernel.lintegral_comp (Kernel.id ×ₖ finiteMarkovKernel K d) (K t) x
    (hF.comp (finiteStateCons_measurable d.length))
  change (∫⁻ p, F (Fin.cons p.1 p.2) ∂((Kernel.id ×ₖ finiteMarkovKernel K d) ∘ₖ K t) x) = _ at hc
  rw [hc]
  apply lintegral_congr
  intro y
  exact Kernel.lintegral_id_prod (hF.comp (finiteStateCons_measurable d.length)) _ y

end TimeTraps.Probability
