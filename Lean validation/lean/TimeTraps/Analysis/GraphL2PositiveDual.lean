module

public import TimeTraps.Analysis.GraphSobolevProduct

@[expose] public section

/-! The nonnegative cone of the actual finite edge L2 product is self-dual.
The proof tests against the genuine L2 negative part; no point evaluation
of an arbitrary L2 class is introduced. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

theorem realL2_inner_negPart {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Lp ℝ 2 μ) : inner ℝ f (Lp.negPart f) = -inner ℝ (Lp.negPart f) (Lp.negPart f) := by
  rw [L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_negPart_eq_max f] with x hx
  simp only [Real.inner_apply, hx]
  by_cases hf : f x ≤ 0
  · rw [max_eq_left (neg_nonneg.mpr hf)]
    ring
  · rw [max_eq_right (neg_nonpos.mpr (le_of_not_ge hf))]
    ring

theorem realL2_nonneg_of_negPart_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Lp ℝ 2 μ) (hf : Lp.negPart f = 0) : ∀ᵐ x ∂μ, 0 ≤ f x := by
  have hz := (Lp.eq_zero_iff_ae_eq_zero).mp hf
  filter_upwards [Lp.coeFn_negPart_eq_max f, hz] with x hx hzero
  change Lp.negPart f x = 0 at hzero
  have hle : -f x ≤ 0 := by
    rw [← hzero, hx]
    exact le_max_left _ _
  exact neg_nonpos.mp hle

theorem graphL2_nonneg_of_positive_pairing {V E : Type*} [Fintype E]
    (G : MetricGraph V E) (f : GraphL2Product G)
    (hf : ∀ g : GraphL2Product G,
      (∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (G.length e)), 0 ≤ (g e) x) → 0 ≤ inner ℝ f g) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (G.length e)), 0 ≤ (f e) x := by
  let g : GraphL2Product G := WithLp.toLp 2 (fun e => Lp.negPart (f e))
  have hg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (G.length e)), 0 ≤ (g e) x := by
    intro e
    exact (Lp.coeFn_negPart_eq_max (f e)).mono (fun _ h => h.symm ▸ le_max_right _ _)
  have hi : inner ℝ f g = -inner ℝ g g := by
    rw [graphL2Product_inner, graphL2Product_inner, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact realL2_inner_negPart (volume.restrict (Ioo 0 (G.length e))) (f e)
  have hz : inner ℝ g g = 0 := by
    have hp := hf g hg
    rw [hi] at hp
    exact le_antisymm (neg_nonneg.mp hp) real_inner_self_nonneg
  have hgzero : g = 0 := inner_self_eq_zero.mp hz
  intro e
  apply realL2_nonneg_of_negPart_zero (volume.restrict (Ioo 0 (G.length e))) (f e)
  exact congrArg (fun q : GraphL2Product G => q e) hgzero

end TimeTraps.Analysis
