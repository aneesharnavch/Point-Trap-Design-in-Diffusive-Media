module

public import TimeTraps.Probability.MarkovFiniteKernelMarginals

@[expose] public section

/-! Mapping the future coordinates of a finite trajectory commutes with
prepending one observed state. This supplies the induction step for true
finite-dimensional consistency under deletion of observation times. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

def finiteStateLift {n m : ℕ} (f : (Fin n → α) → (Fin m → α))
    (q : Fin (n + 1) → α) : Fin (m + 1) → α :=
  Fin.cons (q 0) (f (Fin.tail q))

theorem finiteStateLift_measurable {n m : ℕ} {f : (Fin n → α) → (Fin m → α)}
    (hf : Measurable f) : Measurable (finiteStateLift f) :=
  (finiteStateCons_measurable m).comp
    ((measurable_pi_apply 0).prodMk (hf.comp (finiteStateTail_measurable n)))

set_option backward.isDefEq.respectTransparency false in
theorem finiteMarkovKernel_map_lift (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (t : ℝ≥0) (d : List ℝ≥0) {m : ℕ}
    {f : (Fin d.length → α) → (Fin m → α)} (hf : Measurable f) :
    (finiteMarkovKernel K (t :: d)).map (finiteStateLift f) =
      ((Kernel.id ×ₖ (finiteMarkovKernel K d).map f) ∘ₖ K t).map
        (fun p : α × (Fin m → α) => (Fin.cons p.1 p.2 : Fin (m + 1) → α)) := by
  rw [finiteMarkovKernel, ← Kernel.map_comp_right _
    (finiteStateCons_measurable d.length) (finiteStateLift_measurable hf)]
  have he : finiteStateLift f ∘ (fun p : α × (Fin d.length → α) =>
      (Fin.cons p.1 p.2 : Fin (d.length + 1) → α)) =
      (fun p : α × (Fin m → α) => (Fin.cons p.1 p.2 : Fin (m + 1) → α)) ∘ Prod.map id f := by
    funext p
    simp only [Function.comp_apply, finiteStateLift, Fin.cons_zero, Fin.tail_cons]
    rfl
  rw [he, Kernel.map_comp_right _ (measurable_id.prodMap hf) (finiteStateCons_measurable m),
    Kernel.map_comp, ← Kernel.map_prod_map _ _ measurable_id hf, Kernel.map_id]

theorem finiteMarkovKernel_map_empty (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (d : List ℝ≥0) :
    (finiteMarkovKernel K d).map (fun _ => (Fin.elim0 : Fin 0 → α)) = finiteMarkovKernel K [] := by
  rw [← Kernel.deterministic_comp_eq_map measurable_const]
  change Kernel.const (Fin d.length → α) (Measure.dirac (Fin.elim0 : Fin 0 → α)) ∘ₖ
    finiteMarkovKernel K d = Kernel.const α (Measure.dirac (Fin.elim0 : Fin 0 → α))
  exact Kernel.const_comp' _ _

end TimeTraps.Probability
