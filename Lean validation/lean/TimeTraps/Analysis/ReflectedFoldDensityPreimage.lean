module

public import TimeTraps.Probability.ReflectedFoldAffine
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-! The exact countable fibres of the triangular fold. Its two affine
branches give all preimages, and endpoint preimages are Lebesgue null.
These are deterministic facts, with no diffusion or local-time premise. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Probability
open scoped ENNReal

theorem reflectedFold_eq_iff_lattice (L : ℝ) (hL : 0 < L) (x y : ℝ)
    (hy : y ∈ Icc 0 L) :
    reflectedFold L x = y ↔ ∃ k : ℤ, x = y + k * (2 * L) ∨ x = -y + k * (2 * L) := by
  constructor
  · intro he
    let k : ℤ := round ((2 * L)⁻¹ * x)
    have ha : |x - (k : ℝ) * (2 * L)| = y := (reflectedFold_round L x).symm.trans he
    refine ⟨k, ?_⟩
    by_cases hp : 0 ≤ x - (k : ℝ) * (2 * L)
    · rw [abs_of_nonneg hp] at ha
      exact Or.inl (by linarith)
    · rw [abs_of_neg (lt_of_not_ge hp)] at ha
      exact Or.inr (by linarith)
  · rintro ⟨k, rfl | rfl⟩
    · rw [reflectedFold_int_period, reflectedFold_eq_self L hL y hy]
    · rw [reflectedFold_int_period, reflectedFold_neg, reflectedFold_eq_self L hL y hy]

theorem reflectedFold_preimage_singleton_countable (L : ℝ) (hL : 0 < L) (y : ℝ) :
    ((reflectedFold L) ⁻¹' {y}).Countable := by
  by_cases hy : y ∈ Icc 0 L
  · apply ((countable_range (fun k : ℤ => y + k * (2 * L))).union
      (countable_range (fun k : ℤ => -y + k * (2 * L)))).mono
    intro x hx
    have he : reflectedFold L x = y := hx
    rcases (reflectedFold_eq_iff_lattice L hL x y hy).mp he with ⟨k, hk | hk⟩
    · exact Or.inl ⟨k, hk.symm⟩
    · exact Or.inr ⟨k, hk.symm⟩
  · have he : (reflectedFold L) ⁻¹' {y} = ∅ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hx
      exact hy (hx ▸ reflectedFold_mem L hL x)
    rw [he]
    exact countable_empty

theorem reflectedFold_preimage_singleton_null (L : ℝ) (hL : 0 < L) (y : ℝ) :
    volume ((reflectedFold L) ⁻¹' {y}) = 0 :=
  (reflectedFold_preimage_singleton_countable L hL y).measure_zero volume

theorem reflectedFold_ne_ae (L : ℝ) (hL : 0 < L) (y : ℝ) :
    ∀ᵐ x ∂volume, reflectedFold L x ≠ y := by
  apply ae_iff.mpr
  simpa only [not_not, preimage, mem_singleton_iff] using reflectedFold_preimage_singleton_null L hL y

theorem reflectedFold_interior_ae (L : ℝ) (hL : 0 < L) :
    ∀ᵐ x ∂volume, reflectedFold L x ∈ Ioo 0 L := by
  filter_upwards [reflectedFold_ne_ae L hL 0, reflectedFold_ne_ae L hL L] with x h0 h1
  exact ⟨lt_of_le_of_ne (reflectedFold_nonneg L x) h0.symm,
    lt_of_le_of_ne (reflectedFold_le L hL x) h1⟩

theorem reflectedFold_preimage_branches (L : ℝ) (hL : 0 < L) {s : Set ℝ}
    (hs : s ⊆ Icc 0 L) :
    (reflectedFold L) ⁻¹' s =
      (⋃ k : ℤ, (fun y : ℝ => y + k * (2 * L)) '' s) ∪
      (⋃ k : ℤ, (fun y : ℝ => -y + k * (2 * L)) '' s) := by
  ext x
  constructor
  · intro hx
    rcases (reflectedFold_eq_iff_lattice L hL x (reflectedFold L x) (hs hx)).mp rfl with
      ⟨k, hk | hk⟩
    · exact Or.inl (mem_iUnion.mpr ⟨k, ⟨reflectedFold L x, hx, hk.symm⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, ⟨reflectedFold L x, hx, hk.symm⟩⟩)
  · rintro (hx | hx)
    · rcases mem_iUnion.mp hx with ⟨k, y, hy, rfl⟩
      simpa only [mem_preimage, reflectedFold_int_period, reflectedFold_eq_self L hL y (hs hy)] using hy
    · rcases mem_iUnion.mp hx with ⟨k, y, hy, rfl⟩
      simpa only [mem_preimage, reflectedFold_int_period, reflectedFold_neg,
        reflectedFold_eq_self L hL y (hs hy)] using hy

end TimeTraps.Analysis
