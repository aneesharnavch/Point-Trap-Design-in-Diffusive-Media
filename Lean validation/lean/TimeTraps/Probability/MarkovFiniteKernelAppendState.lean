module

public import TimeTraps.Probability.MarkovFiniteKernelAppendData

@[expose] public section

/-! Exact tuple transport for appending one final observation to the
actual finite elapsed-time list. The only cast records list length. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

def finiteStateSnocCast (d : List ℝ≥0) (t : ℝ≥0) (q : Fin d.length → α) (y : α) :
    Fin (d ++ [t]).length → α :=
  fun i => (Fin.snoc q y : Fin (d.length + 1) → α)
    (Fin.cast (by simp : (d ++ [t]).length = d.length + 1) i)

theorem finiteStateSnocCast_measurable (d : List ℝ≥0) (t : ℝ≥0) :
    Measurable (fun p : (Fin d.length → α) × α => finiteStateSnocCast d t p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (Fin.cast (by simp : (d ++ [t]).length = d.length + 1) i)).comp
    (finiteStateSnoc_measurable d.length)

omit [MeasurableSpace α] in
theorem finiteStateSnocCast_nil (t : ℝ≥0) (q : Fin 0 → α) (y : α) :
    finiteStateSnocCast [] t q y = fun _ => y := rfl

omit [MeasurableSpace α] in
theorem finiteStateSnocCast_cons (s t : ℝ≥0) (d : List ℝ≥0) (y z : α) (q : Fin d.length → α) :
    finiteStateSnocCast (s :: d) t (Fin.cons y q) z =
      Fin.cons y (finiteStateSnocCast d t q z) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [finiteStateSnocCast]
  · change (Fin.snoc (Fin.cons y q) z : Fin (d.length + 2) → α)
      (Fin.succ (Fin.cast (by simp : (d ++ [t]).length = d.length + 1) j)) =
      (Fin.snoc q z : Fin (d.length + 1) → α)
        (Fin.cast (by simp : (d ++ [t]).length = d.length + 1) j)
    rw [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]

theorem finiteStateSnocCast_lintegral_measurable (K : Kernel α α) [IsSFiniteKernel K]
    (d : List ℝ≥0) (t : ℝ≥0) (x : α)
    {F : (Fin (d ++ [t]).length → α) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun q : Fin d.length → α =>
      ∫⁻ y, F (finiteStateSnocCast d t q y) ∂K (finiteStateLast x q)) := by
  let κ : Kernel (Fin d.length → α) α := K.comap (finiteStateLast x) (finiteStateLast_measurable x d.length)
  exact (hF.comp (finiteStateSnocCast_measurable d t)).lintegral_kernel_prod_right' (κ := κ)

end TimeTraps.Probability
