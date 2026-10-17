module

public import TimeTraps.Analysis.ShiftedInverseHeatDerivative
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorCharacterization

@[expose] public section

/-! The right generator of the exponentially translated heat family is
exactly the translated operator on its full actual domain. -/

namespace TimeTraps.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.translatedHeatCurve_unscale {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) (t : ℝ) :
    Real.exp (-c * t) • h.translatedHeatCurve c x t = h.heatCurve x t := by
  rw [translatedHeatCurve, smul_smul, ← Real.exp_add]
  have he : -c * t + c * t = 0 := by ring
  rw [he, Real.exp_zero, one_smul]

theorem CompactPositiveInverse.translatedHeatCurve_right_derivative_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ)
    (x : (translatedInverseOperator T h.injective c).domain) :
    HasDerivWithinAt (h.translatedHeatCurve c (x : E))
      (-translatedInverseOperator T h.injective c x) (Ici 0) 0 := by
  have hd := ((((hasDerivAt_id (0 : ℝ)).const_mul c).exp).hasDerivWithinAt).smul
    (h.heatCurve_right_derivative_zero x)
  simp only [id_eq, mul_zero, Real.exp_zero, one_smul, mul_one, one_mul,
    h.heatCurve_zero] at hd
  have hfun : (fun t => Real.exp (c * t)) • h.heatCurve (x : E) =
      h.translatedHeatCurve c (x : E) := by funext t; rfl
  rw [hfun] at hd
  have he : -translatedInverseOperator T h.injective c x =
      -inverseOperator T h.injective x + c • (x : E) := by
    rw [translatedInverseOperator_apply]
    abel
  rwa [he]

theorem CompactPositiveInverse.translatedHeatCurve_generator_iff {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x v : E) :
    HasDerivWithinAt (h.translatedHeatCurve c x) v (Ici 0) 0 ↔
      ∃ hx : x ∈ (translatedInverseOperator T h.injective c).domain,
        v = -translatedInverseOperator T h.injective c ⟨x, hx⟩ := by
  constructor
  · intro hv
    have hd := ((((hasDerivAt_id (0 : ℝ)).const_mul (-c)).exp).hasDerivWithinAt).smul hv
    simp only [id_eq, mul_zero, Real.exp_zero, one_smul, mul_one, one_mul,
      h.translatedHeatCurve_zero, neg_smul, ← sub_eq_add_neg] at hd
    have hfun : (fun t => Real.exp (-c * t)) • h.translatedHeatCurve c x =
        h.heatCurve x := by
      funext t
      exact h.translatedHeatCurve_unscale c x t
    rw [hfun] at hd
    obtain ⟨hx, he⟩ := (h.heatCurve_generator_iff x (v - c • x)).mp hd
    refine ⟨hx, ?_⟩
    change v = -(inverseOperator T h.injective ⟨x, hx⟩ - c • x)
    have hv' := eq_add_of_sub_eq he
    rw [hv']
    abel
  · rintro ⟨hx, rfl⟩
    exact h.translatedHeatCurve_right_derivative_zero c ⟨x, hx⟩

theorem CompactPositiveInverse.translatedHeatCurve_generator_iff_graph {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x f : E) :
    HasDerivWithinAt (h.translatedHeatCurve c x) (-f) (Ici 0) 0 ↔
      (x, f) ∈ (translatedInverseOperator T h.injective c).graph := by
  rw [h.translatedHeatCurve_generator_iff]
  constructor
  · rintro ⟨hx, he⟩
    have hf := neg_injective he
    rw [hf]
    exact (translatedInverseOperator T h.injective c).mem_graph ⟨x, hx⟩
  · intro hg
    rw [LinearPMap.mem_graph_iff] at hg
    obtain ⟨u, hu, hf⟩ := hg
    change (u : E) = x at hu
    subst x
    exact ⟨u.property, congrArg Neg.neg hf.symm⟩

end TimeTraps.Analysis
