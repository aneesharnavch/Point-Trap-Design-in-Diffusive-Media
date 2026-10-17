module

public import TimeTraps.Probability.MarkovFiniteKernelAppendState

@[expose] public section

/-! Appending an observation to the actual finite trajectory integrates
the original transition from its last state. This identity is derived
from the chronological construction, not from a process Markov premise. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

set_option backward.isDefEq.respectTransparency false in
theorem finiteMarkovKernel_lintegral_append_singleton (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (d : List ℝ≥0) (t : ℝ≥0) (x : α)
    {F : (Fin (d ++ [t]).length → α) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂finiteMarkovKernel K (d ++ [t]) x) =
      ∫⁻ q, ∫⁻ y, F (finiteStateSnocCast d t q y)
        ∂K t (finiteStateLast x q) ∂finiteMarkovKernel K d x := by
  induction d generalizing x with
  | nil =>
      have hc (y : α) (q : Fin 0 → α) : (Fin.cons y q : Fin 1 → α) = fun _ => y := by
        ext i
        have hi : i = 0 := Fin.fin_one_eq_zero i
        subst i
        rfl
      calc
        _ = ∫⁻ y, ∫⁻ q, F (Fin.cons y q) ∂finiteMarkovKernel K [] y ∂K t x :=
          finiteMarkovKernel_lintegral_cons K t [] x hF
        _ = ∫⁻ y, F (fun _ => y) ∂K t x := by
          apply lintegral_congr
          intro y
          simp only [hc, lintegral_const, measure_univ, mul_one]
          rfl
        _ = _ := by
          change (∫⁻ y, F (fun _ => y) ∂K t x) =
            ∫⁻ _q : Fin 0 → α, (∫⁻ y, F (fun _ => y) ∂K t x) ∂finiteMarkovKernel K [] x
          have hr := lintegral_const (μ := finiteMarkovKernel K [] x)
            (∫⁻ y, F (fun _ => y) ∂K t x)
          rw [measure_univ, mul_one] at hr
          exact hr.symm
  | cons s d ih =>
      have hH := finiteStateSnocCast_lintegral_measurable (K t) (s :: d) t x hF
      calc
        _ = ∫⁻ y, ∫⁻ q, F (Fin.cons y q) ∂finiteMarkovKernel K (d ++ [t]) y ∂K s x :=
          finiteMarkovKernel_lintegral_cons K s (d ++ [t]) x hF
        _ = ∫⁻ y, ∫⁻ q, ∫⁻ z, F (finiteStateSnocCast (s :: d) t (Fin.cons y q) z)
            ∂K t (finiteStateLast x (Fin.cons y q)) ∂finiteMarkovKernel K d y ∂K s x := by
          apply lintegral_congr
          intro y
          have hFy : Measurable (fun q : Fin (d ++ [t]).length → α => F (Fin.cons y q)) :=
            hF.comp ((finiteStateCons_measurable (d ++ [t]).length).comp
              (measurable_const.prodMk measurable_id))
          apply (ih y hFy).trans
          apply lintegral_congr
          intro q
          rw [finiteStateLast_cons]
          apply lintegral_congr
          intro z
          rw [finiteStateSnocCast_cons]
        _ = _ := by
          exact (finiteMarkovKernel_lintegral_cons K s d x hH).symm

end TimeTraps.Probability
