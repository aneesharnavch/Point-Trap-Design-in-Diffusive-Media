module

public import TimeTraps.Probability.MarkovFiniteKernelMap

@[expose] public section

/-! Measurable last-state and append operations for the actual finite
trajectory tuples. The starting state is retained for an empty past. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

def finiteStateLast (x : α) : {n : ℕ} → (Fin n → α) → α
  | 0, _ => x
  | n + 1, q => q (Fin.last n)

omit [MeasurableSpace α] in
theorem finiteStateLast_cons (x y : α) {n : ℕ} (q : Fin n → α) :
    finiteStateLast x (Fin.cons y q) = finiteStateLast y q := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem finiteStateLast_measurable (x : α) (n : ℕ) :
    Measurable (finiteStateLast x : (Fin n → α) → α) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply (Fin.last n)

theorem finiteStateSnoc_measurable (n : ℕ) :
    Measurable (fun p : (Fin n → α) × α => (Fin.snoc p.1 p.2 : Fin (n + 1) → α)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (fun p : (Fin n → α) × α => p.2))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      ((measurable_pi_apply j).comp (measurable_fst : Measurable (fun p : (Fin n → α) × α => p.1)))

theorem finiteStateSnoc_lintegral_measurable (K : Kernel α α) [IsSFiniteKernel K]
    (x : α) {n : ℕ} {F : (Fin (n + 1) → α) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun q : Fin n → α => ∫⁻ y, F (Fin.snoc q y) ∂K (finiteStateLast x q)) := by
  let κ : Kernel (Fin n → α) α := K.comap (finiteStateLast x) (finiteStateLast_measurable x n)
  exact (hF.comp (finiteStateSnoc_measurable n)).lintegral_kernel_prod_right' (κ := κ)

end TimeTraps.Probability
