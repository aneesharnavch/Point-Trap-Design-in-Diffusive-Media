module

public import TimeTraps.Probability.BrownianPredictableDensitySpace

@[expose] public section

/-! The predictable generators and complements belong to the actual
closed elementary integral space after restriction to a finite horizon. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable [IsFiniteMeasure P]

theorem brownianPredictableDensityMember_tail (T s : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[brownianNaturalFiltration B hBm s] A) :
    BrownianPredictableDensityMember B hBm P
      (brownianPredictableCutoffIndicator T (Ioi s ×ˢ A)) := by
  rw [brownianPredictableCutoffIndicator_tail]
  by_cases hst : s ≤ T
  · have hf := brownianPredictableRectangle_memLp (P := P) s T hst A hA 1
    exact ⟨hf.toLp _, brownianPredictableRectangle_mem_integralSpace s T hst A hA 1 hf,
      hf.coeFn_toLp⟩
  · have hts : T.val ≤ s.val := NNReal.coe_le_coe.mpr (le_of_not_ge hst)
    rw [Ioc_eq_empty_of_le hts, empty_prod, indicator_empty]
    exact brownianPredictableDensityMember_zero

theorem brownianPredictableDensityMember_univ (T : ℝ≥0) :
    BrownianPredictableDensityMember B hBm P
      (brownianPredictableCutoffIndicator T (univ : Set (ℝ≥0 × Ω))) := by
  let a := brownianPredictableRectangleElementary (B := B) (hBm := hBm) (P := P)
    0 T (show (0 : ℝ≥0) ≤ T from zero_le) univ MeasurableSet.univ 1
  refine ⟨a.processL2, (brownianIntegralGenerator a).property, ?_⟩
  apply a.processL2_coe.trans
  apply Filter.Eventually.of_forall
  intro p
  rw [brownianPredictableCutoffIndicator_univ]
  change brownianElementaryProcess 0 T (univ.indicator (fun _ : Ω => (1 : ℝ))) p = _
  rw [indicator_univ]

theorem brownianPredictableDensityMember_generator (T : ℝ≥0)
    (E : Set (ℝ≥0 × Ω))
    (hE : E ∈ brownianPredictableGenerators (brownianNaturalFiltration B hBm)) :
    BrownianPredictableDensityMember B hBm P (brownianPredictableCutoffIndicator T E) := by
  rcases hE with ⟨A, _, rfl⟩ | ⟨s, A, hA, rfl⟩
  · rw [brownianPredictableCutoffIndicator_zero_time]
    exact brownianPredictableDensityMember_zero
  · exact brownianPredictableDensityMember_tail T s A hA

theorem brownianPredictableDensityMember_compl (T : ℝ≥0) (E : Set (ℝ≥0 × Ω))
    (hE : BrownianPredictableDensityMember B hBm P (brownianPredictableCutoffIndicator T E)) :
    BrownianPredictableDensityMember B hBm P (brownianPredictableCutoffIndicator T Eᶜ) := by
  rw [brownianPredictableCutoffIndicator_compl]
  exact brownianPredictableDensityMember_sub (brownianPredictableDensityMember_univ T) hE

end TimeTraps.Probability
