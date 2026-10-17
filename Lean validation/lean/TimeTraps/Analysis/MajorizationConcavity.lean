module

public import TimeTraps.Analysis.Majorization
public import TimeTraps.Analysis.ConcaveTangent

@[expose] public section

/-! Differentiable Karamata inequalities from supporting tangents and exact
summation by parts, with strict equality classification by permutations. -/

namespace TimeTraps.Analysis

open Set
open scoped BigOperators

variable {n : ℕ} {S : Set ℝ} {f : ℝ → ℝ}

theorem deriv_weighted_sum_nonpos_of_prefix (hf : ConcaveOn ℝ S f)
    (hfd : ∀ t ∈ S, DifferentiableAt ℝ f t) (x y : Fin n → ℝ)
    (hy : ∀ i, y i ∈ S) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) :
    (∑ i, deriv f (y i) * (x i - y i)) ≤ 0 := by
  apply weighted_sum_nonpos_of_prefix
  · intro i j hij
    exact (hf.antitoneOn_deriv hfd) (hy j) (hy i) (hanti hij)
  · rw [Finset.sum_sub_distrib, htotal, sub_self]
  · intro k hk
    rw [vectorPrefix_sub]
    exact sub_nonneg.mpr (hp k hk)

theorem concave_sum_le_of_prefix (hf : ConcaveOn ℝ S f)
    (hfd : ∀ t ∈ S, DifferentiableAt ℝ f t) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) :
    (∑ i, f (x i)) ≤ ∑ i, f (y i) := by
  have hs : (∑ i, f (x i)) ≤ ∑ i, (f (y i) + deriv f (y i) * (x i - y i)) :=
    Finset.sum_le_sum fun i _ => concave_tangent_le hf (hx i) (hy i) (hfd _ (hy i)).hasDerivAt
  rw [Finset.sum_add_distrib] at hs
  have hz := deriv_weighted_sum_nonpos_of_prefix hf hfd x y hy hanti htotal hp
  linarith

theorem strictConcave_sum_lt_of_prefix (hf : StrictConcaveOn ℝ S f)
    (hfd : ∀ t ∈ S, DifferentiableAt ℝ f t) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) (hne : x ≠ y) :
    (∑ i, f (x i)) < ∑ i, f (y i) := by
  obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, x i = y i from fun h => hne (funext h))
  have hs : (∑ i, f (x i)) < ∑ i, (f (y i) + deriv f (y i) * (x i - y i)) :=
    Finset.sum_lt_sum
      (fun j _ => concave_tangent_le hf.concaveOn (hx j) (hy j) (hfd _ (hy j)).hasDerivAt)
      ⟨i, Finset.mem_univ i, strictConcave_tangent_lt hf (hx i) (hy i) (hfd _ (hy i)).hasDerivAt hi⟩
  rw [Finset.sum_add_distrib] at hs
  have hz := deriv_weighted_sum_nonpos_of_prefix hf.concaveOn hfd x y hy hanti htotal hp
  linarith

theorem Majorizes.concave_sum_le {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : ConcaveOn ℝ S f) (hfd : ∀ t ∈ S, DifferentiableAt ℝ f t)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    (∑ i, f (x i)) ≤ ∑ i, f (y i) := by
  have hs := concave_sum_le_of_prefix hf hfd (descending x) (descending y)
    (fun i => hx (descendingOrder x i)) (fun i => hy (descendingOrder y i)) (descending_antitone y)
    (show (∑ i, descending x i) = ∑ i, descending y i by
      rw [descending_sum, descending_sum]; exact h.total) h.prefix_le
  simpa only [descending_map_sum] using hs

theorem Majorizes.strictConcave_sum_lt {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : StrictConcaveOn ℝ S f) (hfd : ∀ t ∈ S, DifferentiableAt ℝ f t)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) :
    (∑ i, f (x i)) < ∑ i, f (y i) := by
  have hsort : descending x ≠ descending y := fun he => hne ((descending_eq_iff_permuted x y).mp he)
  have hs := strictConcave_sum_lt_of_prefix hf hfd (descending x) (descending y)
    (fun i => hx (descendingOrder x i)) (fun i => hy (descendingOrder y i)) (descending_antitone y)
    (show (∑ i, descending x i) = ∑ i, descending y i by
      rw [descending_sum, descending_sum]; exact h.total) h.prefix_le hsort
  simpa only [descending_map_sum] using hs

theorem Majorizes.strictConcave_sum_eq_iff {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : StrictConcaveOn ℝ S f) (hfd : ∀ t ∈ S, DifferentiableAt ℝ f t)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    (∑ i, f (x i)) = ∑ i, f (y i) ↔ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  constructor
  · intro he
    by_contra hne
    exact (h.strictConcave_sum_lt hf hfd hx hy hne).ne he
  · intro hperm
    have hs := (descending_eq_iff_permuted x y).mpr hperm
    calc
      (∑ i, f (x i)) = ∑ i, f (descending x i) := (descending_map_sum f x).symm
      _ = ∑ i, f (descending y i) := by rw [hs]
      _ = ∑ i, f (y i) := descending_map_sum f y

end TimeTraps.Analysis
