module

public import TimeTraps.Analysis.ReflectedFoldDensityPreimage
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

/-! Disjoint interior branches and their exact Lebesgue changes of
variables. Every branch has absolute slope one. The density may be
extended nonnegative, with no finiteness or integrability requirement. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped ENNReal Function

theorem reflectedFold_branch_index_unique (L : ℝ) (hL : 0 < L)
    {y z : ℝ} (hy : y ∈ Ioo (-L) L) (hz : z ∈ Ioo (-L) L) {k j : ℤ}
    (he : y + k * (2 * L) = z + j * (2 * L)) : k = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hk | hk
  · have hkj : (k : ℝ) + 1 ≤ j := by exact_mod_cast (Int.add_one_le_iff.mpr hk)
    have hm := mul_le_mul_of_nonneg_right hkj (show 0 ≤ 2 * L by positivity)
    nlinarith [hy.2, hz.1]
  · have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr hk)
    have hm := mul_le_mul_of_nonneg_right hjk (show 0 ≤ 2 * L by positivity)
    nlinarith [hy.1, hz.2]

theorem reflectedFold_rising_pairwiseDisjoint (L : ℝ) (hL : 0 < L)
    {s : Set ℝ} (hs : s ⊆ Ioo 0 L) :
    Pairwise (Disjoint on (fun k : ℤ => (fun y : ℝ => y + k * (2 * L)) '' s)) := by
  intro k j hkj
  apply disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ ⟨z, hz, he⟩
  exact hkj (reflectedFold_branch_index_unique L hL
    ⟨by linarith [(hs hy).1], (hs hy).2⟩
    ⟨by linarith [(hs hz).1], (hs hz).2⟩ he.symm)

theorem reflectedFold_falling_pairwiseDisjoint (L : ℝ) (hL : 0 < L)
    {s : Set ℝ} (hs : s ⊆ Ioo 0 L) :
    Pairwise (Disjoint on (fun k : ℤ => (fun y : ℝ => k * (2 * L) - y) '' s)) := by
  intro k j hkj
  apply disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ ⟨z, hz, he⟩
  exact hkj (reflectedFold_branch_index_unique L hL
    (y := -y) (z := -z) ⟨by linarith [(hs hy).2], by linarith [(hs hy).1]⟩
    ⟨by linarith [(hs hz).2], by linarith [(hs hz).1]⟩ (by linarith))

theorem reflectedFold_rising_falling_disjoint (L : ℝ) (hL : 0 < L)
    {s : Set ℝ} (hs : s ⊆ Ioo 0 L) :
    Disjoint (⋃ k : ℤ, (fun y : ℝ => y + k * (2 * L)) '' s)
      (⋃ k : ℤ, (fun y : ℝ => k * (2 * L) - y) '' s) := by
  apply disjoint_left.mpr
  intro x hx hx'
  rcases mem_iUnion.mp hx with ⟨k, y, hy, rfl⟩
  rcases mem_iUnion.mp hx' with ⟨j, z, hz, he⟩
  have hkj : k = j := reflectedFold_branch_index_unique L hL
    (y := y) (z := -z) ⟨by linarith [(hs hy).1], (hs hy).2⟩
    ⟨by linarith [(hs hz).2], by linarith [(hs hz).1]⟩ (by linarith)
  subst j
  linarith [(hs hy).1, (hs hz).1]

theorem reflectedFold_rising_lintegral (c : ℝ) (s : Set ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in (fun y : ℝ => y + c) '' s, f x) = ∫⁻ y in s, f (y + c) :=
  ((measurePreserving_add_right volume c).setLIntegral_comp_emb
    (MeasurableEquiv.addRight c).measurableEmbedding f s).symm

theorem reflectedFold_falling_lintegral (c : ℝ) (s : Set ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in (fun y : ℝ => c - y) '' s, f x) = ∫⁻ y in s, f (c - y) :=
  ((volume.measurePreserving_sub_left c).setLIntegral_comp_emb
    (MeasurableEquiv.subLeft c).measurableEmbedding f s).symm

end TimeTraps.Analysis
