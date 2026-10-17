module

public import TimeTraps.Graph.GeometryOptimum

@[expose] public section

/-!
Common-diffusivity specializations of the attained graph optimum. Passive
pendants contribute half an effective cell. The final count specialization
is a graph theorem; identifying an ordered interval design remains separate.
-/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped BigOperators Classical

variable {V E : Type*} [Fintype E] [Nonempty E]

noncomputable def GeometryProblem.pendantEdges (P : GeometryProblem V E) : Finset E :=
  Finset.univ.filter fun e => P.passive (P.tail e) ∨ P.passive (P.head e)

noncomputable def GeometryProblem.effectiveCells (P : GeometryProblem V E) : ℝ :=
  (Fintype.card E : ℝ) - (P.pendantEdges.card : ℝ) / 2

theorem GeometryProblem.effectiveCells_pos (P : GeometryProblem V E) : 0 < P.effectiveCells := by
  have hc : P.pendantEdges.card ≤ Fintype.card E := by
    simpa only [GeometryProblem.pendantEdges, Finset.card_univ] using Finset.card_le_card
      (Finset.filter_subset (fun e => P.passive (P.tail e) ∨ P.passive (P.head e)) Finset.univ)
  have hcr : (P.pendantEdges.card : ℝ) ≤ (Fintype.card E : ℝ) := by exact_mod_cast hc
  have hE : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  unfold GeometryProblem.effectiveCells
  linarith

omit [Fintype E] [Nonempty E] in
theorem GeometryProblem.scale_common (P : GeometryProblem V E) {D : ℝ}
    (hD : 0 < D) (hd : ∀ e, P.diffusivity e = D) (e : E) :
    P.scale e = if P.passive (P.tail e) ∨ P.passive (P.head e) then Real.sqrt D / 2 else Real.sqrt D := by
  by_cases hp : P.passive (P.tail e) ∨ P.passive (P.head e)
  · have hs : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    simp [GeometryProblem.scale, GeometryProblem.reflection, hd e, hp, Real.sqrt_div hD.le, hs]
  · simp [GeometryProblem.scale, GeometryProblem.reflection, hd e, hp]

omit [Nonempty E] in
theorem GeometryProblem.totalScale_common (P : GeometryProblem V E) {D : ℝ}
    (hD : 0 < D) (hd : ∀ e, P.diffusivity e = D) :
    P.totalScale = Real.sqrt D * P.effectiveCells := by
  calc
    _ = ∑ e, (Real.sqrt D -
        (if P.passive (P.tail e) ∨ P.passive (P.head e) then (1 : ℝ) else 0) * (Real.sqrt D / 2)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [P.scale_common hD hd e]
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_boole]
      unfold GeometryProblem.effectiveCells GeometryProblem.pendantEdges
      ring

omit [Nonempty E] in
theorem GeometryProblem.optimalValue_common (P : GeometryProblem V E) {D : ℝ}
    (hD : 0 < D) (hd : ∀ e, P.diffusivity e = D) (L K : ℝ) :
    P.optimalValue L K = L / K + L ^ 2 / (8 * D * P.effectiveCells ^ 2) := by
  unfold GeometryProblem.optimalValue
  rw [P.totalScale_common hD hd, mul_pow, Real.sq_sqrt hD.le]
  ring

theorem GeometryProblem.optimalLengths_common (P : GeometryProblem V E) {D : ℝ}
    (hD : 0 < D) (hd : ∀ e, P.diffusivity e = D) (L : ℝ) (e : E) :
    P.optimalLengths L e =
      if P.passive (P.tail e) ∨ P.passive (P.head e) then L / (2 * P.effectiveCells)
      else L / P.effectiveCells := by
  unfold GeometryProblem.optimalLengths
  rw [P.totalScale_common hD hd, P.scale_common hD hd e]
  split_ifs <;> field_simp [ne_of_gt (Real.sqrt_pos.mpr hD), ne_of_gt P.effectiveCells_pos]

/-- The effective-cell formula is an attained minimum over actual designs. -/
theorem GeometryProblem.common_diffusivity_minimum [Fintype V] (P : GeometryProblem V E)
    {D L K : ℝ} (hD : 0 < D) (hd : ∀ e, P.diffusivity e = D) (hL : 0 < L) (hK : 0 < K) :
    IsLeast (P.designValues L K) (L / K + L ^ 2 / (8 * D * P.effectiveCells ^ 2)) := by
  rw [← P.optimalValue_common hD hd L K]
  exact P.geometry_minimum hL hK

theorem GeometryProblem.effectiveCells_from_counts (P : GeometryProblem V E) (m b : ℕ)
    (he : Fintype.card E = m + 1) (hp : P.pendantEdges.card + b = 2) :
    P.effectiveCells = (2 * (m : ℝ) + b) / 2 ∧ 0 < 2 * m + b := by
  have hpr : (P.pendantEdges.card : ℝ) + b = 2 := by exact_mod_cast hp
  have heq : P.effectiveCells = (2 * (m : ℝ) + b) / 2 := by
    unfold GeometryProblem.effectiveCells
    rw [he]
    push_cast
    linarith
  refine ⟨heq, ?_⟩
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + b := by
    have hc := P.effectiveCells_pos
    rw [heq] at hc
    linarith
  exact_mod_cast hpos

/-- The interval-style count expression under the stated graph counts. This
does not replace the separate ordered-interval/metric-graph identification. -/
theorem GeometryProblem.count_specialized_minimum [Fintype V] (P : GeometryProblem V E)
    {D L K : ℝ} (hD : 0 < D) (hd : ∀ e, P.diffusivity e = D) (hL : 0 < L) (hK : 0 < K)
    (m b : ℕ) (he : Fintype.card E = m + 1) (hp : P.pendantEdges.card + b = 2) :
    IsLeast (P.designValues L K) (L / K + L ^ 2 / (2 * D * (2 * (m : ℝ) + b) ^ 2)) := by
  have hm := P.common_diffusivity_minimum hD hd hL hK
  rw [(P.effectiveCells_from_counts m b he hp).1] at hm
  have hden : 8 * D * ((2 * (m : ℝ) + b) / 2) ^ 2 = 2 * D * (2 * (m : ℝ) + b) ^ 2 := by ring
  rwa [hden] at hm

end TimeTraps.Graph
