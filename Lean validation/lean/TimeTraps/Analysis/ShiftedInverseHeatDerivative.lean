module

public import TimeTraps.Analysis.ShiftedInverseHeat
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! At positive time the translated heat family solves the actual
translated operator equation for every Hilbert initial state. -/

namespace TimeTraps.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.translatedHeatCurve_hasDerivAt {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (h.translatedHeatCurve c x)
      (-translatedInverseOperator T h.injective c
        ⟨h.translatedHeatCurve c x s, h.translatedHeatCurve_mem_domain_of_pos c x hs⟩) s := by
  let u : (inverseOperator T h.injective).domain :=
    ⟨h.heatCurve x s, h.heatCurve_mem_domain_of_pos x hs⟩
  have hd := (((hasDerivAt_id s).const_mul c).exp).smul (h.heatCurve_hasDerivAt_of_pos x hs)
  have he : -translatedInverseOperator T h.injective c
      ⟨h.translatedHeatCurve c x s, h.translatedHeatCurve_mem_domain_of_pos c x hs⟩ =
      Real.exp (c * s) • (-inverseOperator T h.injective u) +
        (Real.exp (c * s) * c) • h.heatCurve x s := by
    change -(inverseOperator T h.injective (Real.exp (c * s) • u) -
      c • (Real.exp (c * s) • h.heatCurve x s)) = _
    rw [LinearPMap.map_smul, smul_smul, mul_comm c (Real.exp (c * s)), smul_neg, neg_sub]
    abel
  rw [he]
  simp only [id_eq, mul_one] at hd
  have hfun : (fun t => Real.exp (c * t)) • h.heatCurve x = h.translatedHeatCurve c x := by
    funext t
    rfl
  rw [hfun] at hd
  exact hd

theorem CompactPositiveInverse.translatedHeatCurve_deriv {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) {s : ℝ} (hs : 0 < s) :
    deriv (h.translatedHeatCurve c x) s =
      -translatedInverseOperator T h.injective c
        ⟨h.translatedHeatCurve c x s, h.translatedHeatCurve_mem_domain_of_pos c x hs⟩ :=
  (h.translatedHeatCurve_hasDerivAt c x hs).deriv

theorem CompactPositiveInverse.translatedHeatCurve_deriv_graph {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) {s : ℝ} (hs : 0 < s) :
    (h.translatedHeatCurve c x s, -deriv (h.translatedHeatCurve c x) s) ∈
      (translatedInverseOperator T h.injective c).graph := by
  rw [h.translatedHeatCurve_deriv c x hs, neg_neg]
  exact (translatedInverseOperator T h.injective c).mem_graph
    ⟨_, h.translatedHeatCurve_mem_domain_of_pos c x hs⟩

end TimeTraps.Analysis
