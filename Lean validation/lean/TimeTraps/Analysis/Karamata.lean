module

public import TimeTraps.Analysis.Majorization
public import TimeTraps.Analysis.KaramataSupport

@[expose] public section

/-! Karamata's inequality for convex functions on an arbitrary convex real
domain, with no differentiability assumption. Strict convexity characterizes
equality exactly by permutation. Concave forms follow by negation. -/

namespace TimeTraps.Analysis

open Set
open scoped BigOperators

variable {n : ℕ} {S : Set ℝ} {f : ℝ → ℝ}

theorem support_weighted_sum_nonneg_of_prefix {T : Set ℝ} {c : ℝ → ℝ}
    (hc : ∀ a ∈ T, ∀ z ∈ T, f a + c a * (z - a) ≤ f z)
    (x y : Fin n → ℝ) (hy : ∀ i, y i ∈ T) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) :
    0 ≤ ∑ i, c (y i) * (x i - y i) := by
  have hn := weighted_sum_nonpos_of_prefix
    (fun i => -c (y i)) (fun i => x i - y i)
    (show Monotone (fun i => -c (y i)) from fun i j hij =>
      neg_le_neg ((finite_support_monotoneOn hc) (hy j) (hy i) (hanti hij)))
    (show (∑ i, (x i - y i)) = 0 by rw [Finset.sum_sub_distrib, htotal, sub_self])
    (fun k hk => by rw [vectorPrefix_sub]; exact sub_nonneg.mpr (hp k hk))
  simpa only [neg_mul, Finset.sum_neg_distrib, neg_nonpos] using hn

theorem convex_sum_le_of_prefix (hf : ConvexOn ℝ S f) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) :
    (∑ i, f (y i)) ≤ ∑ i, f (x i) := by
  classical
  let T := Finset.univ.image x ∪ Finset.univ.image y
  have hTx (i) : x i ∈ T := Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)
  have hTy (i) : y i ∈ T := Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)
  have hT : ∀ z ∈ T, z ∈ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hxz | hyz
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxz
      exact hx i
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hyz
      exact hy i
  have hex : ∀ a : ℝ, ∃ c : ℝ, a ∈ T →
      ∀ z ∈ T, f a + c * (z - a) ≤ f z := by
    intro a
    by_cases ha : a ∈ T
    · obtain ⟨c, hc⟩ := convex_finite_support_exists hf T hT (hT a ha)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose c hc using hex
  have hz := support_weighted_sum_nonneg_of_prefix (T := (T : Set ℝ))
    hc x y hTy hanti htotal hp
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hc (y i) (hTy i) (x i) (hTx i))
  rw [Finset.sum_add_distrib] at hs
  linarith

theorem strictConvex_sum_lt_of_prefix (hf : StrictConvexOn ℝ S f) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) (hne : x ≠ y) :
    (∑ i, f (y i)) < ∑ i, f (x i) := by
  classical
  let T := Finset.univ.image x ∪ Finset.univ.image y
  have hTx (i) : x i ∈ T := Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)
  have hTy (i) : y i ∈ T := Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)
  have hT : ∀ z ∈ T, z ∈ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hxz | hyz
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxz
      exact hx i
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hyz
      exact hy i
  have hex : ∀ a : ℝ, ∃ c : ℝ, a ∈ T →
      ∀ z ∈ T, z ≠ a → f a + c * (z - a) < f z := by
    intro a
    by_cases ha : a ∈ T
    · obtain ⟨c, hc⟩ := strictConvex_finite_support_exists hf T hT (hT a ha)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose c hc using hex
  have hcle : ∀ a ∈ T, ∀ z ∈ T, f a + c a * (z - a) ≤ f z := by
    intro a ha z hz
    by_cases hza : z = a
    · simp [hza]
    · exact (hc a ha z hz hza).le
  have hz := support_weighted_sum_nonneg_of_prefix (T := (T : Set ℝ))
    hcle x y hTy hanti htotal hp
  obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, x i = y i from fun h => hne (funext h))
  have hs := Finset.sum_lt_sum
    (fun j (_ : j ∈ Finset.univ) => hcle (y j) (hTy j) (x j) (hTx j))
    ⟨i, Finset.mem_univ i, hc (y i) (hTy i) (x i) (hTx i) hi⟩
  rw [Finset.sum_add_distrib] at hs
  linarith

theorem Majorizes.convex_sum_le {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : ConvexOn ℝ S f) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    (∑ i, f (y i)) ≤ ∑ i, f (x i) := by
  have hs := convex_sum_le_of_prefix hf (descending x) (descending y)
    (fun i => hx (descendingOrder x i)) (fun i => hy (descendingOrder y i))
    (descending_antitone y)
    (show (∑ i, descending x i) = ∑ i, descending y i by
      rw [descending_sum, descending_sum]; exact h.total) h.prefix_le
  simpa only [descending_map_sum] using hs

theorem Majorizes.strictConvex_sum_lt {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : StrictConvexOn ℝ S f) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) :
    (∑ i, f (y i)) < ∑ i, f (x i) := by
  have hsort : descending x ≠ descending y :=
    fun he => hne ((descending_eq_iff_permuted x y).mp he)
  have hs := strictConvex_sum_lt_of_prefix hf (descending x) (descending y)
    (fun i => hx (descendingOrder x i)) (fun i => hy (descendingOrder y i))
    (descending_antitone y)
    (show (∑ i, descending x i) = ∑ i, descending y i by
      rw [descending_sum, descending_sum]; exact h.total) h.prefix_le hsort
  simpa only [descending_map_sum] using hs

theorem Majorizes.strictConvex_sum_eq_iff {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : StrictConvexOn ℝ S f) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    (∑ i, f (x i)) = ∑ i, f (y i) ↔ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  constructor
  · intro he
    by_contra hne
    exact (h.strictConvex_sum_lt hf hx hy hne).ne he.symm
  · intro hperm
    have hs := (descending_eq_iff_permuted x y).mpr hperm
    calc
      (∑ i, f (x i)) = ∑ i, f (descending x i) := (descending_map_sum f x).symm
      _ = ∑ i, f (descending y i) := by rw [hs]
      _ = ∑ i, f (y i) := descending_map_sum f y

theorem Majorizes.concave_sum_le_general {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : ConcaveOn ℝ S f) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    (∑ i, f (x i)) ≤ ∑ i, f (y i) := by
  have hs := h.convex_sum_le hf.neg hx hy
  simpa only [Pi.neg_apply, Finset.sum_neg_distrib, neg_le_neg_iff] using hs

theorem Majorizes.strictConcave_sum_lt_general {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : StrictConcaveOn ℝ S f) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) :
    (∑ i, f (x i)) < ∑ i, f (y i) := by
  have hs := h.strictConvex_sum_lt hf.neg hx hy hne
  simpa only [Pi.neg_apply, Finset.sum_neg_distrib, neg_lt_neg_iff] using hs

theorem Majorizes.strictConcave_sum_eq_iff_general {x y : Fin n → ℝ} (h : Majorizes x y)
    (hf : StrictConcaveOn ℝ S f) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    (∑ i, f (x i)) = ∑ i, f (y i) ↔ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  have hs := h.strictConvex_sum_eq_iff hf.neg hx hy
  simpa only [Pi.neg_apply, Finset.sum_neg_distrib, neg_inj] using hs

end TimeTraps.Analysis
