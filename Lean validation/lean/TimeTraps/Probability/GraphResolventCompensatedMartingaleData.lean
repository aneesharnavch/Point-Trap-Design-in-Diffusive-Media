module

public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! Finite real linear combinations preserve the martingale identity.
The statement uses literal scalar processes to match the point-source
resolvent decomposition. -/

namespace TimeTraps.Probability

open MeasureTheory

variable {I Ω ι : Type*} [Fintype I] [MeasurableSpace Ω] [Preorder ι]


theorem graphResolventMartingale_sub_sum
    (ℱ : Filtration ι (inferInstance : MeasurableSpace Ω)) (μ : Measure Ω)
    (F : ι → Ω → ℝ) (M : I → ι → Ω → ℝ) (c : I → ℝ)
    (hF : Martingale F ℱ μ) (hM : ∀ i, Martingale (M i) ℱ μ) :
    Martingale (fun t p => F t p - ∑ i, c i * M i t p) ℱ μ := by
  classical
  have hs (s : Finset I) : Martingale (fun t p => ∑ i ∈ s, c i * M i t p) ℱ μ := by
    induction s using Finset.induction_on with
    | empty =>
      have hz := martingale_zero ℝ ℱ μ
      change Martingale (fun _ _ => 0) ℱ μ at hz
      simpa only [Finset.sum_empty] using hz
    | @insert a s ha ih =>
      have he := (Martingale.smul (c a) (hM a)).add ih
      change Martingale (fun t p => c a * M a t p + ∑ i ∈ s, c i * M i t p) ℱ μ at he
      simpa only [Finset.sum_insert ha] using he
  exact hF.sub (hs Finset.univ)

end TimeTraps.Probability
